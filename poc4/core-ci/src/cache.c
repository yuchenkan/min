#include "cache.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define CACHE_MAGIC "MINC"
#define CACHE_VERSION 1

typedef uint64_t Addr;

/* ---- write helpers ---- */

static void wr_u32(CacheOps *ops, void *f, uint32_t v) { ops->fwrite(&v, 4, 1, f); }
static void wr_u64(CacheOps *ops, void *f, uint64_t v) { ops->fwrite(&v, 8, 1, f); }
static void wr_i64(CacheOps *ops, void *f, int64_t v) { ops->fwrite(&v, 8, 1, f); }

static void wr_str(CacheOps *ops, void *f, const char *s) {
  uint32_t len = strlen(s);
  wr_u32(ops, f, len);
  ops->fwrite(s, 1, len, f);
}

/* ---- read helpers ---- */

static int rd_u32(CacheOps *ops, void *f, uint32_t *v) {
  return ops->fread(v, 4, 1, f) == 1 ? 0 : -1;
}

static int rd_u64(CacheOps *ops, void *f, uint64_t *v) {
  return ops->fread(v, 8, 1, f) == 1 ? 0 : -1;
}

static int rd_i64(CacheOps *ops, void *f, int64_t *v) {
  return ops->fread(v, 8, 1, f) == 1 ? 0 : -1;
}

static int rd_str(CacheOps *ops, void *f, char **out) {
  uint32_t len;
  if (rd_u32(ops, f, &len)) return -1;
  char *s = malloc(len + 1);
  if (ops->fread(s, 1, len, f) != len) { free(s); return -1; }
  s[len] = '\0';
  *out = s;
  return 0;
}

/* ---- save ---- */

enum { S_STR = 1, S_NODE = 2, S_ENV = 3 };

/* pointer hash set */
typedef struct { void **b; int cap, n; } PSet;

static void pset_init(PSet *s) { s->cap = 256; s->n = 0; s->b = calloc(256, sizeof(void *)); }
static void pset_free(PSet *s) { free(s->b); }

static int pset_idx(PSet *s, void *p) {
  return (int)(((uint64_t)(uintptr_t)p >> 4) * 2654435761ULL & (uint64_t)(s->cap - 1));
}

static void pset_add(PSet *s, void *p);

static int pset_has(PSet *s, void *p) {
  for (int i = pset_idx(s, p);; i = (i + 1) & (s->cap - 1)) {
    if (!s->b[i]) return 0;
    if (s->b[i] == p) return 1;
  }
}

static void pset_grow(PSet *s) {
  PSet old = *s;
  s->cap *= 2; s->n = 0; s->b = calloc(s->cap, sizeof(void *));
  for (int i = 0; i < old.cap; i++)
    if (old.b[i]) pset_add(s, old.b[i]);
  free(old.b);
}

static void pset_add(PSet *s, void *p) {
  if (s->n * 2 >= s->cap) pset_grow(s);
  for (int i = pset_idx(s, p);; i = (i + 1) & (s->cap - 1)) {
    if (!s->b[i]) { s->b[i] = p; s->n++; return; }
    if (s->b[i] == p) return;
  }
}

/* graph save context */
typedef struct {
  CacheOps *ops;
  void *f;
  PSet seen;
  Env *global;
} GCtx;

static void ga(GCtx *g, void *p) { wr_u64(g->ops, g->f, (Addr)(uintptr_t)p); }

/* section 1: modules — (addr, mtime, string)* 0 */
static int write_module_cb(const char *key, void *val, void *ctx) {
  GCtx *g = ctx;
  Module *mod = val;
  wr_u64(g->ops, g->f, (Addr)(uintptr_t)key);
  wr_i64(g->ops, g->f, mod->mtime);
  wr_str(g->ops, g->f, key);
  pset_add(&g->seen, (void *)key);
  return 0;
}

/* section 2: import relations — (addr, import_addrs..., 0)* 0 */
static int write_import_addr_cb(void *item, void *ctx) {
  GCtx *g = ctx;
  wr_u64(g->ops, g->f, (Addr)(uintptr_t)(const char *)item);
  return 0;
}

static int write_deps_cb(const char *key, void *val, void *ctx) {
  GCtx *g = ctx;
  Module *mod = val;
  wr_u64(g->ops, g->f, (Addr)(uintptr_t)key);
  gc_list_each(mod->imports, write_import_addr_cb, g);
  wr_u64(g->ops, g->f, 0);
  return 0;
}

/* ---- object graph ---- */

static int gnew(GCtx *g, void *p) {
  if (!p || pset_has(&g->seen, p)) return 0;
  pset_add(&g->seen, p);
  return 1;
}

/* collect GCList items */
typedef struct { void **items; int n, cap; } Bag;

static int bag_cb(void *item, void *ctx) {
  Bag *b = ctx;
  if (b->n == b->cap) { b->cap *= 2; b->items = realloc(b->items, b->cap * sizeof(void *)); }
  b->items[b->n++] = item;
  return 0;
}

static Bag bag_list(GCList *list) {
  Bag b = { malloc(8 * sizeof(void *)), 0, 8 };
  if (list) gc_list_each(list, bag_cb, &b);
  return b;
}

/* collect GCMap entries */
typedef struct { const char **keys; void **vals; int n, cap; } MapBag;

static int mapbag_cb(const char *key, void *val, void *ctx) {
  MapBag *m = ctx;
  if (m->n == m->cap) {
    m->cap *= 2;
    m->keys = realloc(m->keys, m->cap * sizeof(const char *));
    m->vals = realloc(m->vals, m->cap * sizeof(void *));
  }
  m->keys[m->n] = key; m->vals[m->n] = val; m->n++;
  return 0;
}

static MapBag bag_env(Env *e) {
  MapBag m = { malloc(8 * sizeof(const char *)), malloc(8 * sizeof(void *)), 0, 8 };
  env_each(e, mapbag_cb, &m);
  return m;
}

static void gsave_str(GCtx *g, const char *s);
static void gsave_node(GCtx *g, Node *n);
static void gsave_env(GCtx *g, Env *e);

static void gsave_str(GCtx *g, const char *s) {
  if (!gnew(g, (void *)s)) return;
  ga(g, (void *)s);
  wr_u32(g->ops, g->f, S_STR);
  wr_str(g->ops, g->f, s);
}

static void gsave_env(GCtx *g, Env *e) {
  if (!e || e == g->global) return;
  if (!gnew(g, e)) return;

  MapBag m = bag_env(e);

  /* recurse children first (post-order) */
  gsave_env(g, e->parent);
  for (int i = 0; i < m.n; i++) { gsave_str(g, m.keys[i]); gsave_node(g, m.vals[i]); }

  /* write: addr, S_ENV, parent_addr, (key_addr, val_addr)* 0 */
  ga(g, e); wr_u32(g->ops, g->f, S_ENV);
  ga(g, e->parent);
  for (int i = 0; i < m.n; i++) { ga(g, (void *)m.keys[i]); ga(g, m.vals[i]); }
  wr_u64(g->ops, g->f, 0);

  free(m.keys); free(m.vals);
}

static void gsave_node(GCtx *g, Node *n) {
  if (!gnew(g, n)) return;

  /* recurse children first (post-order) */
  gsave_str(g, n->file);

  switch (n->tag) {
  case N_INT: break;
  case N_STR: gsave_str(g, n->str); break;
  case N_TRUE: case N_FALSE: case N_NONE:
    assert(0 && "singleton in object graph");
    break;
  case N_ARR: {
    Node **elems = n->arr.data;
    for (uint64_t i = 0; i < n->arr.len; i++) gsave_node(g, elems[i]);
    break;
  }
  case N_PROOF:
    gsave_node(g, n->proof.left); gsave_node(g, n->proof.right);
    break;
  case N_CLOSURE: {
    Bag params = bag_list(n->closure.params);
    gsave_node(g, n->closure.body); gsave_env(g, n->closure.env);
    for (int i = 0; i < params.n; i++) gsave_str(g, params.items[i]);
    free(params.items);
    break;
  }
  case N_REF: gsave_str(g, n->ref); break;
  case N_FN: {
    Bag params = bag_list(n->fn.params);
    gsave_node(g, n->fn.body);
    for (int i = 0; i < params.n; i++) gsave_str(g, params.items[i]);
    free(params.items);
    break;
  }
  case N_CALL: {
    Bag args = bag_list(n->call.args);
    gsave_node(g, n->call.callee);
    for (int i = 0; i < args.n; i++) gsave_node(g, args.items[i]);
    free(args.items);
    break;
  }
  case N_IF:
    gsave_node(g, n->if_.cond); gsave_node(g, n->if_.then); gsave_node(g, n->if_.else_);
    break;
  case N_BLOCK: {
    Bag binds = bag_list(n->block.binds);
    gsave_node(g, n->block.expr);
    for (int i = 0; i < binds.n; i++) gsave_node(g, binds.items[i]);
    free(binds.items);
    break;
  }
  case N_BIND:
    gsave_str(g, n->bind.name); gsave_node(g, n->bind.expr);
    break;
  case N_LIST: {
    Bag items = bag_list(n->list);
    for (int i = 0; i < items.n; i++) gsave_node(g, items.items[i]);
    free(items.items);
    break;
  }
  case N_IMPORT:
    assert(0 && "N_IMPORT in runtime env");
    break;
  case N_BUILTIN:
    assert(0 && "N_BUILTIN in object graph");
    break;
  }

  /* write: addr, S_NODE, tag, file_addr, line, col, tag-specific addrs */
  ga(g, n); wr_u32(g->ops, g->f, S_NODE);
  wr_u32(g->ops, g->f, (uint32_t)n->tag);
  ga(g, (void *)n->file);
  wr_u32(g->ops, g->f, (uint32_t)n->line);
  wr_u32(g->ops, g->f, (uint32_t)n->col);

  switch (n->tag) {
  case N_INT: wr_u64(g->ops, g->f, n->integer); break;
  case N_STR: ga(g, n->str); break;
  case N_ARR: {
    wr_u64(g->ops, g->f, n->arr.len);
    Node **elems = n->arr.data;
    for (uint64_t i = 0; i < n->arr.len; i++) ga(g, elems[i]);
    break;
  }
  case N_PROOF: ga(g, n->proof.left); ga(g, n->proof.right); break;
  case N_CLOSURE: {
    Bag params = bag_list(n->closure.params);
    ga(g, n->closure.body); ga(g, n->closure.env);
    for (int i = 0; i < params.n; i++) ga(g, params.items[i]);
    wr_u64(g->ops, g->f, 0);
    free(params.items);
    break;
  }
  case N_REF: ga(g, n->ref); break;
  case N_FN: {
    Bag params = bag_list(n->fn.params);
    ga(g, n->fn.body);
    for (int i = 0; i < params.n; i++) ga(g, params.items[i]);
    wr_u64(g->ops, g->f, 0);
    free(params.items);
    break;
  }
  case N_CALL: {
    Bag args = bag_list(n->call.args);
    ga(g, n->call.callee);
    for (int i = 0; i < args.n; i++) ga(g, args.items[i]);
    wr_u64(g->ops, g->f, 0);
    free(args.items);
    break;
  }
  case N_IF: ga(g, n->if_.cond); ga(g, n->if_.then); ga(g, n->if_.else_); break;
  case N_BLOCK: {
    Bag binds = bag_list(n->block.binds);
    ga(g, n->block.expr);
    for (int i = 0; i < binds.n; i++) ga(g, binds.items[i]);
    wr_u64(g->ops, g->f, 0);
    free(binds.items);
    break;
  }
  case N_BIND: ga(g, n->bind.name); ga(g, n->bind.expr); break;
  case N_LIST: {
    Bag items = bag_list(n->list);
    for (int i = 0; i < items.n; i++) ga(g, items.items[i]);
    wr_u64(g->ops, g->f, 0);
    free(items.items);
    break;
  }
  default: break;
  }
}

/* save global env entries: (val_addr, name_addr, name_string)* 0 */
static int save_global_cb(const char *key, void *val, void *ctx) {
  GCtx *g = ctx;
  wr_u64(g->ops, g->f, (Addr)(uintptr_t)val);
  wr_u64(g->ops, g->f, (Addr)(uintptr_t)key);
  wr_str(g->ops, g->f, key);
  pset_add(&g->seen, val);
  pset_add(&g->seen, (void *)key);
  return 0;
}

/* write module env mapping: (filepath_addr, env_addr) */
static int write_env_map_cb(const char *key, void *val, void *ctx) {
  GCtx *g = ctx;
  Module *mod = val;
  wr_u64(g->ops, g->f, (Addr)(uintptr_t)key);
  wr_u64(g->ops, g->f, (Addr)(uintptr_t)mod->env);
  return 0;
}

/* save module env graph */
static int save_env_graph_cb(const char *key, void *val, void *ctx) {
  (void)key;
  GCtx *g = ctx;
  Module *mod = val;
  gsave_env(g, mod->env);
  return 0;
}

int cache_save(const char *path, GC *gc, GCMap *modules, Env *global, CacheOps *ops) {
  (void)gc;
  void *f = ops->fopen(path, "wb");
  if (!f) return -1;

  ops->fwrite(CACHE_MAGIC, 1, 4, f);
  wr_u32(ops, f, CACHE_VERSION);

  GCtx g = { ops, f, {0}, global };
  pset_init(&g.seen);

  /* section 1: modules — (filepath_str_addr, mtime, string)* 0 */
  gc_map_each(modules, write_module_cb, &g);
  wr_u64(ops, f, 0);

  /* section 2: import relations — (addr, import_addrs..., 0)* 0 */
  gc_map_each(modules, write_deps_cb, &g);
  wr_u64(ops, f, 0);

  /* section 3: global address table — global_addr, (val_addr, name)* 0 */
  wr_u64(ops, f, (Addr)(uintptr_t)global);
  env_each(global, save_global_cb, &g);
  wr_u64(ops, f, 0);

  /* section 4: module env mapping — (filepath_addr, env_addr)* 0 */
  gc_map_each(modules, write_env_map_cb, &g);
  wr_u64(ops, f, 0);

  /* section 5: object graph — (addr, type, data...)* 0 */
  gc_map_each(modules, save_env_graph_cb, &g);
  wr_u64(ops, f, 0);

  pset_free(&g.seen);
  ops->fclose(f);
  return 0;
}

/* ---- load ---- */

typedef struct {
  Addr addr;
  const char *filepath;
  int64_t mtime;
  Addr *imports;
  int nimports;
  int cap_imports;
  int valid;
} CacheEntry;

static void free_entries(CacheEntry *entries, int n) {
  for (int i = 0; i < n; i++)
    free(entries[i].imports);
  free(entries);
}

static CacheEntry *find_entry(CacheEntry *entries, int n, Addr addr) {
  for (int i = 0; i < n; i++)
    if (entries[i].addr == addr) return &entries[i];
  return NULL;
}

static void check_valid(CacheEntry *entries, int n, CacheEntry *e) {
  if (e->valid != 1) return;
  e->valid = 0; /* mark visiting — breaks cycles */
  for (int j = 0; j < e->nimports; j++) {
    CacheEntry *dep = find_entry(entries, n, e->imports[j]);
    if (!dep) return;
    check_valid(entries, n, dep);
    if (dep->valid != 2) return;
  }
  e->valid = 2;
}

/* ---- addr map: old ptr -> new ptr ---- */

typedef struct { Addr key; void *val; } AEntry;
typedef struct { AEntry *e; int cap, n; } AMap;

static int amap_idx(AMap *m, Addr k) {
  return (int)((k >> 4) * 2654435761ULL & (uint64_t)(m->cap - 1));
}

static void **amap_put(GC *gc, AMap *m, Addr k);

static void amap_grow(GC *gc, AMap *m) {
  AMap old = *m;
  m->cap *= 2; m->n = 0;
  m->e = gc_alloc(gc, m->cap * sizeof(AEntry), NULL, NULL, NULL);
  memset(m->e, 0, m->cap * sizeof(AEntry));
  for (int i = 0; i < old.cap; i++)
    if (old.e[i].key) *amap_put(gc, m, old.e[i].key) = old.e[i].val;
}

static void **amap_put(GC *gc, AMap *m, Addr k) {
  if (m->n * 2 >= m->cap) amap_grow(gc, m);
  for (int i = amap_idx(m, k);; i = (i + 1) & (m->cap - 1)) {
    if (!m->e[i].key) { m->e[i].key = k; m->n++; return &m->e[i].val; }
    if (m->e[i].key == k) return &m->e[i].val;
  }
}

static void *amap_get(AMap *m, Addr k) {
  if (!k) return NULL;
  for (int i = amap_idx(m, k);; i = (i + 1) & (m->cap - 1)) {
    if (!m->e[i].key) return NULL;
    if (m->e[i].key == k) return m->e[i].val;
  }
}

static void amap_trace(void *data) {
  AMap *m = data;
  if (!m->e) return;
  gc_mark(m->e);
  for (int i = 0; i < m->cap; i++)
    if (m->e[i].key) gc_mark(m->e[i].val);
}

/* ---- buffer cursor ---- */

typedef struct { const uint8_t *d; size_t p, n; } Cur;

static void cu32(Cur *c, uint32_t *v) {
  if (c->p + 4 > c->n) return;
  memcpy(v, c->d + c->p, 4); c->p += 4;
}

static void cu64(Cur *c, uint64_t *v) {
  if (c->p + 8 > c->n) return;
  memcpy(v, c->d + c->p, 8); c->p += 8;
}

/* collect null-terminated addr list into temp array */
static Addr *read_addrs(Cur *c, int *count) {
  int n = 0, cap = 8;
  Addr *a = malloc(cap * sizeof(Addr));
  for (;;) {
    Addr v = 0; cu64(c, &v);
    if (v == 0) break;
    if (n == cap) { cap *= 2; a = realloc(a, cap * sizeof(Addr)); }
    a[n++] = v;
  }
  *count = n;
  return a;
}



/* ---- load ---- */

int cache_load(const char *path, GC *gc, Intern *it, GCMap *modules, Env *global, void **slot, CacheOps *ops) {
  void *f = ops->fopen(path, "rb");
  if (!f) return 0;

  char magic[4];
  if (ops->fread(magic, 1, 4, f) != 4 || memcmp(magic, CACHE_MAGIC, 4) != 0) {
    ops->fclose(f); return 0;
  }
  uint32_t version;
  if (rd_u32(ops, f, &version) || version != CACHE_VERSION) {
    ops->fclose(f); return 0;
  }

  AMap *amap = gc_alloc(gc, sizeof(AMap), amap_trace, NULL, NULL);
  amap->cap = 256; amap->n = 0; amap->e = NULL;
  *slot = amap;
  amap->e = gc_alloc(gc, 256 * sizeof(AEntry), NULL, NULL, NULL);
  memset(amap->e, 0, 256 * sizeof(AEntry));

  /* section 1: modules — (addr, mtime, string)* 0 */
  int nentries = 0, cap_entries = 16;
  CacheEntry *entries = calloc(cap_entries, sizeof(CacheEntry));
  for (;;) {
    Addr addr;
    if (rd_u64(ops, f, &addr)) goto fail;
    if (addr == 0) break;
    if (nentries == cap_entries) {
      cap_entries *= 2;
      entries = realloc(entries, cap_entries * sizeof(CacheEntry));
      memset(&entries[nentries], 0, (cap_entries - nentries) * sizeof(CacheEntry));
    }
    CacheEntry *e = &entries[nentries++];
    e->addr = addr;
    if (rd_i64(ops, f, &e->mtime)) goto fail;
    char *fp;
    if (rd_str(ops, f, &fp)) goto fail;
    e->filepath = intern(it, fp);
    free(fp);
    e->valid = 1;
    *amap_put(gc, amap, addr) = (void *)e->filepath;
  }

  /* section 2: import relations — (addr, import_addrs..., 0)* 0 */
  for (;;) {
    Addr addr;
    if (rd_u64(ops, f, &addr)) goto fail;
    if (addr == 0) break;
    CacheEntry *e = find_entry(entries, nentries, addr);
    if (!e) goto fail;
    e->cap_imports = 8;
    e->imports = calloc(e->cap_imports, sizeof(Addr));
    e->nimports = 0;
    for (;;) {
      Addr imp;
      if (rd_u64(ops, f, &imp)) goto fail;
      if (imp == 0) break;
      if (e->nimports == e->cap_imports) {
        e->cap_imports *= 2;
        e->imports = realloc(e->imports, e->cap_imports * sizeof(Addr));
      }
      e->imports[e->nimports++] = imp;
    }
  }

  /* check mtimes */
  for (int i = 0; i < nentries; i++) {
    if (!entries[i].valid) continue;
    int64_t cur = ops->mtime(entries[i].filepath);
    if (cur != entries[i].mtime)
      entries[i].valid = 0;
  }

  /* transitive invalidation */
  for (int i = 0; i < nentries; i++)
    check_valid(entries, nentries, &entries[i]);

  int nvalid = 0;
  for (int i = 0; i < nentries; i++)
    if (entries[i].valid == 2) nvalid++;
  if (nvalid == 0) {
    ops->fclose(f);
    free_entries(entries, nentries);
    return 0;
  }

  /* section 3: global address table */
  Addr global_addr;
  if (rd_u64(ops, f, &global_addr)) goto fail;
  *amap_put(gc, amap, global_addr) = global;
  for (;;) {
    Addr va;
    if (rd_u64(ops, f, &va)) goto fail;
    if (va == 0) break;
    Addr na;
    if (rd_u64(ops, f, &na)) goto fail;
    char *name;
    if (rd_str(ops, f, &name)) goto fail;
    const char *iname = intern(it, name);
    *amap_put(gc, amap, na) = (void *)iname;
    Node **s = env_find(global, iname);
    assert(s);
    *amap_put(gc, amap, va) = *s;
    free(name);
  }

  /* section 4: module env mapping — (filepath_addr, env_addr)* 0 */
  Addr *mod_fps = malloc(nentries * sizeof(Addr));
  Addr *mod_envs = malloc(nentries * sizeof(Addr));
  int nmod = 0;
  for (;;) {
    Addr fp;
    if (rd_u64(ops, f, &fp)) { free(mod_fps); free(mod_envs); goto fail; }
    if (fp == 0) break;
    Addr ea;
    if (rd_u64(ops, f, &ea)) { free(mod_fps); free(mod_envs); goto fail; }
    mod_fps[nmod] = fp;
    mod_envs[nmod] = ea;
    nmod++;
  }

  /* read section 5 into buffer */
  size_t buf_cap = 4096, buf_len = 0;
  uint8_t *buf = malloc(buf_cap);
  { uint8_t chunk[4096]; size_t nr;
    while ((nr = ops->fread(chunk, 1, sizeof(chunk), f)) > 0) {
      if (buf_len + nr > buf_cap) {
        while (buf_len + nr > buf_cap) buf_cap *= 2;
        buf = realloc(buf, buf_cap);
      }
      memcpy(buf + buf_len, chunk, nr);
      buf_len += nr;
    }
  }
  ops->fclose(f);
  f = NULL;

  /* single pass: create objects, resolve references, register in addr map */
  { Cur c = { buf, 0, buf_len };
    for (;;) {
      Addr addr = 0; cu64(&c, &addr); if (addr == 0) break;
      uint32_t type = 0; cu32(&c, &type);

      if (type == S_STR) {
        uint32_t len = 0; cu32(&c, &len);
        char tmp[len + 1];
        memcpy(tmp, c.d + c.p, len); tmp[len] = '\0'; c.p += len;
        *amap_put(gc, amap, addr) = (void *)intern(it, tmp);

      } else if (type == S_NODE) {
        uint32_t tag = 0; cu32(&c, &tag);
        Addr fa = 0; uint32_t line = 0, col = 0;
        cu64(&c, &fa); cu32(&c, &line); cu32(&c, &col);

        if (tag == N_INT) {
          uint64_t val = 0; cu64(&c, &val);
          *amap_put(gc, amap, addr) = intern_int(it, val);
        } else if (tag == N_STR) {
          Addr sa = 0; cu64(&c, &sa);
          *amap_put(gc, amap, addr) = intern_str(it, amap_get(amap, sa));
        } else if (tag == N_ARR) {
          uint64_t len = 0; cu64(&c, &len);
          Node **elems = len ? malloc(len * sizeof(Node *)) : NULL;
          for (uint64_t i = 0; i < len; i++) { Addr ea = 0; cu64(&c, &ea); elems[i] = amap_get(amap, ea); }
          void **nslot = amap_put(gc, amap, addr);
          intern_arr(it, elems, len, nslot);
          free(elems);
        } else if (tag == N_TRUE) {
          *amap_put(gc, amap, addr) = intern_true(it);
        } else if (tag == N_FALSE) {
          *amap_put(gc, amap, addr) = intern_false(it);
        } else if (tag == N_NONE) {
          *amap_put(gc, amap, addr) = intern_none(it);
        } else {
          void **nslot = amap_put(gc, amap, addr);
          Node *n = gc_alloc(gc, sizeof(Node), node_trace, NULL, NULL);
          memset(n, 0, sizeof(Node));
          n->tag = tag;
          n->file = amap_get(amap, fa);
          n->line = (int)line;
          n->col = (int)col;
          *nslot = n;

          switch (tag) {
          case N_PROOF: {
            Addr la = 0, ra = 0; cu64(&c, &la); cu64(&c, &ra);
            n->proof.left = amap_get(amap, la); n->proof.right = amap_get(amap, ra);
            break;
          }
          case N_CLOSURE: {
            Addr ba = 0, ea = 0; cu64(&c, &ba); cu64(&c, &ea);
            n->closure.body = amap_get(amap, ba);
            n->closure.env = amap_get(amap, ea);
            n->closure.params = gc_list_new(gc);
            int np = 0; Addr *pa = read_addrs(&c, &np);
            for (int i = 0; i < np; i++)
              *gc_list_append(gc, n->closure.params) = amap_get(amap, pa[i]);
            free(pa);
            n->closure.cache = gc_cc_new(gc, np);
            break;
          }
          case N_REF: { Addr ra = 0; cu64(&c, &ra); n->ref = amap_get(amap, ra); break; }
          case N_FN: {
            Addr ba = 0; cu64(&c, &ba);
            n->fn.body = amap_get(amap, ba);
            n->fn.params = gc_list_new(gc);
            int np = 0; Addr *pa = read_addrs(&c, &np);
            for (int i = 0; i < np; i++)
              *gc_list_append(gc, n->fn.params) = amap_get(amap, pa[i]);
            free(pa);
            break;
          }
          case N_CALL: {
            Addr ca = 0; cu64(&c, &ca);
            n->call.callee = amap_get(amap, ca);
            n->call.args = gc_list_new(gc);
            int na = 0; Addr *aa = read_addrs(&c, &na);
            for (int i = 0; i < na; i++)
              *gc_list_append(gc, n->call.args) = amap_get(amap, aa[i]);
            free(aa);
            break;
          }
          case N_IF: {
            Addr ca = 0, ta = 0, ea = 0; cu64(&c, &ca); cu64(&c, &ta); cu64(&c, &ea);
            n->if_.cond = amap_get(amap, ca);
            n->if_.then = amap_get(amap, ta);
            n->if_.else_ = amap_get(amap, ea);
            break;
          }
          case N_BLOCK: {
            Addr ea = 0; cu64(&c, &ea);
            n->block.expr = amap_get(amap, ea);
            n->block.binds = gc_list_new(gc);
            int nb = 0; Addr *ba = read_addrs(&c, &nb);
            for (int i = 0; i < nb; i++)
              *gc_list_append(gc, n->block.binds) = amap_get(amap, ba[i]);
            free(ba);
            break;
          }
          case N_BIND: {
            Addr na2 = 0, ea = 0; cu64(&c, &na2); cu64(&c, &ea);
            n->bind.name = amap_get(amap, na2);
            n->bind.expr = amap_get(amap, ea);
            break;
          }
          case N_LIST: {
            n->list = gc_list_new(gc);
            int ni = 0; Addr *ia = read_addrs(&c, &ni);
            for (int i = 0; i < ni; i++)
              *gc_list_append(gc, n->list) = amap_get(amap, ia[i]);
            free(ia);
            break;
          }
          default: break;
          }
        }

      } else if (type == S_ENV) {
        void **eslot = amap_put(gc, amap, addr);
        env_new(gc, eslot);
        Env *e = *eslot;
        Addr pa = 0; cu64(&c, &pa);
        e->parent = amap_get(amap, pa);
        for (;;) {
          Addr ka = 0; cu64(&c, &ka);
          if (ka == 0) break;
          Addr va = 0; cu64(&c, &va);
          *env_get(gc, e, amap_get(amap, ka)) = amap_get(amap, va);
        }
      }
    }
  }

  free(buf);

  /* mount valid modules */
  int loaded = 0;
  for (int i = 0; i < nmod; i++) {
    CacheEntry *ce = find_entry(entries, nentries, mod_fps[i]);
    if (!ce || ce->valid != 2) continue;

    Env *env = amap_get(amap, mod_envs[i]);
    if (!env) continue;

    void **mslot = gc_map_get(gc, modules, ce->filepath);
    Module *mod = gc_alloc(gc, sizeof(Module), module_trace, NULL, NULL);
    mod->env = env;
    mod->mtime = ce->mtime;
    mod->imports = NULL;
    *mslot = mod;
    mod->imports = gc_list_new(gc);
    for (int j = 0; j < ce->nimports; j++)
      *gc_list_append(gc, mod->imports) = amap_get(amap, ce->imports[j]);
    loaded++;
  }

  *slot = NULL;
  free(mod_fps);
  free(mod_envs);
  free_entries(entries, nentries);
  return loaded;

fail:
  if (f) ops->fclose(f);
  *slot = NULL;
  free_entries(entries, nentries);
  return 0;
}
