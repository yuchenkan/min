#include "gc.h"
#include "htable.h"
#include <stdlib.h>
#include <string.h>

typedef struct GCObject GCObject;

struct GCObject {
  GCObject *prev;
  GCObject *next;
  GCTraceFn trace;
  GCFreeFn free_fn;
  void *free_ctx;
  size_t size;
  unsigned char mark;
};

struct GC {
  GCObject sentinel;
  GCObject *root;
  size_t total;
  size_t threshold;
  size_t min_thresh;
  size_t max_thresh;
};

static void gc_link(GC *gc, GCObject *obj) {
  obj->next = gc->sentinel.next;
  obj->prev = &gc->sentinel;
  gc->sentinel.next->prev = obj;
  gc->sentinel.next = obj;
}

static void gc_unlink(GCObject *obj) {
  obj->prev->next = obj->next;
  obj->next->prev = obj->prev;
}

static void *obj_data(GCObject *obj) {
  return (char *)obj + sizeof(GCObject);
}

static GCObject *data_obj(void *data) {
  return (GCObject *)((char *)data - sizeof(GCObject));
}

static void gc_sweep(GC *gc) {
  size_t alive = 0;
  GCObject *obj = gc->sentinel.next;
  while (obj != &gc->sentinel) {
    GCObject *next = obj->next;
    if (!obj->mark) {
      gc_unlink(obj);
      if (obj->free_fn) obj->free_fn(obj_data(obj), obj->free_ctx);
      gc->total -= obj->size;
      free(obj);
    } else {
      alive += obj->size;
      obj->mark = 0;
    }
    obj = next;
  }
  size_t t = alive * 2;
  if (t < gc->min_thresh) t = gc->min_thresh;
  if (t > gc->max_thresh) t = gc->max_thresh;
  gc->threshold = t;
}

void *gc_init(size_t root_size, GCTraceFn root_trace, size_t min_thresh, size_t max_thresh, GC **out) {
  GC *gc = malloc(sizeof(GC));
  gc->sentinel.prev = &gc->sentinel;
  gc->sentinel.next = &gc->sentinel;
  gc->total = 0;
  gc->min_thresh = min_thresh;
  gc->max_thresh = max_thresh;
  gc->threshold = min_thresh;

  gc->root = NULL;
  void *root = gc_alloc(gc, root_size, root_trace, NULL, NULL);
  gc->root = data_obj(root);
  *out = gc;
  return root;
}

void gc_fini(GC *gc) {
  GCObject *obj = gc->sentinel.next;
  while (obj != &gc->sentinel) {
    GCObject *next = obj->next;
    if (obj->free_fn) obj->free_fn(obj_data(obj), obj->free_ctx);
    free(obj);
    obj = next;
  }
  free(gc);
}

void *gc_alloc(GC *gc, size_t size, GCTraceFn trace_fn, GCFreeFn free_fn, void *free_ctx) {
  if (gc->root && gc->total >= gc->threshold) {
    gc_mark(obj_data(gc->root));
    gc_sweep(gc);
  }
  GCObject *obj = malloc(sizeof(GCObject) + size);
  obj->trace = trace_fn;
  obj->free_fn = free_fn;
  obj->free_ctx = free_ctx;
  obj->size = sizeof(GCObject) + size;
  obj->mark = 0;
  gc_link(gc, obj);
  gc->total += obj->size;
  return obj_data(obj);
}


void gc_mark(void *data) {
  if (!data) return;
  GCObject *obj = data_obj(data);
  if (obj->mark) return;
  obj->mark = 1;
  if (obj->trace) obj->trace(data);
}

/* append-only singly-linked list */

typedef struct GCListNode GCListNode;

struct GCListNode {
  void *item;
  GCListNode *next;
};

struct GCList {
  GCListNode *head;
  GCListNode **tail;
};

static void gc_list_node_trace(void *data) {
  GCListNode *node = data;
  gc_mark(node->item);
  gc_mark(node->next);
}

static void gc_list_trace(void *data) {
  GCList *list = data;
  gc_mark(list->head);
}

GCList *gc_list_new(GC *gc) {
  GCList *list = gc_alloc(gc, sizeof(GCList), gc_list_trace, NULL, NULL);
  list->head = NULL;
  list->tail = &list->head;
  return list;
}

void **gc_list_append(GC *gc, GCList *list) {
  GCListNode *node = gc_alloc(gc, sizeof(GCListNode), gc_list_node_trace, NULL, NULL);
  node->item = NULL;
  node->next = NULL;
  *list->tail = node;
  list->tail = &node->next;
  return &node->item;
}

int gc_list_each(GCList *list, GCListFn fn, void *ctx) {
  for (GCListNode *node = list->head; node; node = node->next) {
    int err = fn(node->item, ctx);
    if (err) return err;
  }
  return 0;
}

/* string-to-void* map backed by hash table */

#define GC_MAP_INIT_CAP 16

static int gc_ptr_eq(const void *a, const void *b) { return a == b; }
static uint64_t gc_ptr_hash(const void *p) { return (uintptr_t)p; }

struct GCMap {
  HTable ht;
  GC *gc;
};

static void gc_ht_trace(HTable *ht) {
  if (!ht->entries) return;
  gc_mark(ht->entries);
  for (int i = 0; i < ht->cap; i++) {
    HTEntry *e = &ht->entries[i];
    if (e->key && e->key != HT_TOMB) {
      gc_mark((void *)e->key);
      gc_mark(e->val);
    }
  }
}

static void gc_map_trace(void *data) {
  GCMap *m = data;
  gc_ht_trace(&m->ht);
}

static void gc_ht_resize(GC *gc, HTable *t, int newcap) {
  HTable fresh;
  fresh.entries = gc_alloc(gc, sizeof(HTEntry) * newcap, NULL, NULL, NULL);
  fresh.cap = newcap;
  fresh.count = 0;
  fresh.ghost = 0;
  memset(fresh.entries, 0, sizeof(HTEntry) * newcap);
  ht_rehash(&fresh, t, gc_ptr_hash);
  *t = fresh;
}

static void gc_ht_maybe_resize(GC *gc, HTable *t) {
  if (ht_needs_grow(t))
    gc_ht_resize(gc, t, t->cap * 2);
  else if (ht_needs_shrink(t, GC_MAP_INIT_CAP))
    gc_ht_resize(gc, t, t->cap / 2);
}

static void gc_ht_ensure(GC *gc, HTable *ht) {
  if (!ht->entries) {
    ht->cap = GC_MAP_INIT_CAP;
    ht->entries = gc_alloc(gc, sizeof(HTEntry) * GC_MAP_INIT_CAP, NULL, NULL, NULL);
    memset(ht->entries, 0, sizeof(HTEntry) * GC_MAP_INIT_CAP);
  }
}

GCMap *gc_map_new(GC *gc) {
  GCMap *m = gc_alloc(gc, sizeof(GCMap), gc_map_trace, NULL, NULL);
  memset(m, 0, sizeof(GCMap));
  m->gc = gc;
  return m;
}

void **gc_map_get(GC *gc, GCMap *map, const char *key) {
  gc_ht_ensure(gc, &map->ht);
  gc_ht_maybe_resize(gc, &map->ht);
  return ht_get(&map->ht, (uintptr_t)key, (void *)key, gc_ptr_eq);
}

void gc_map_delete(GCMap *map, const char *key) {
  if (!map->ht.entries) return;
  ht_del(&map->ht, (uintptr_t)key, key, gc_ptr_eq);
  gc_ht_maybe_resize(map->gc, &map->ht);
}

void **gc_map_find(GCMap *map, const char *key) {
  if (!map->ht.entries) return NULL;
  return ht_find(&map->ht, (uintptr_t)key, key, gc_ptr_eq);
}

void gc_map_copy(GC *gc, void **slot, GCMap *src) {
  GCMap *dst = gc_alloc(gc, sizeof(GCMap), gc_map_trace, NULL, NULL);
  memset(dst, 0, sizeof(GCMap));
  dst->gc = gc;
  *slot = dst;
  if (src->ht.entries) {
    dst->ht.cap = src->ht.cap;
    dst->ht.entries = gc_alloc(gc, sizeof(HTEntry) * src->ht.cap, NULL, NULL, NULL);
    memset(dst->ht.entries, 0, sizeof(HTEntry) * src->ht.cap);
    ht_rehash(&dst->ht, &src->ht, gc_ptr_hash);
  }
}

/* call cache: flat open-addressing, keys are inline arg sequences */

#define CC_INIT_CAP 16

struct GCCallCache {
  void *data;   /* gc_alloc'd: (nargs+1) * cap pointers, [arg0..argN, result] per slot */
  int nargs;
  int cap;
  int count;
};

static void gc_cc_trace(void *d) {
  GCCallCache *cc = d;
  if (!cc->data) return;
  gc_mark(cc->data);
  int stride = cc->nargs + 1;
  void **arr = cc->data;
  for (int i = 0; i < cc->cap; i++) {
    int base = i * stride;
    if (arr[base])
      for (int j = 0; j < stride; j++)
        gc_mark(arr[base + j]);
  }
}

static uint64_t cc_hash(void **args, int n) {
  uint64_t h = (uint64_t)n;
  for (int i = 0; i < n; i++)
    h = h * 0x9e3779b97f4a7c15ULL + (uintptr_t)args[i];
  return h;
}

static int cc_slot(uint64_t hash, int mask) {
  return (int)((hash * 0x9e3779b97f4a7c15ULL) >> 32) & mask;
}

GCCallCache *gc_cc_new(GC *gc, int nargs) {
  GCCallCache *cc = gc_alloc(gc, sizeof(GCCallCache), gc_cc_trace, NULL, NULL);
  cc->data = NULL;
  cc->nargs = nargs;
  cc->cap = 0;
  cc->count = 0;
  return cc;
}

void **gc_cc_find(GCCallCache *cc, void **args) {
  if (!cc->data) return NULL;
  int stride = cc->nargs + 1;
  int n = cc->nargs;
  void **arr = cc->data;
  int mask = cc->cap - 1;
  for (int i = cc_slot(cc_hash(args, n), mask); ; i = (i + 1) & mask) {
    int base = i * stride;
    if (!arr[base]) return NULL;
    int match = 1;
    for (int j = 0; j < n; j++)
      if (arr[base + j] != args[j]) { match = 0; break; }
    if (match) return &arr[base + n];
  }
}

void **gc_cc_get(GC *gc, GCCallCache *cc, void **args) {
  int stride = cc->nargs + 1;
  int n = cc->nargs;
  if (!cc->data) {
    cc->cap = CC_INIT_CAP;
    cc->data = gc_alloc(gc, sizeof(void *) * stride * CC_INIT_CAP, NULL, NULL, NULL);
    memset(cc->data, 0, sizeof(void *) * stride * CC_INIT_CAP);
  }
  if (cc->count * 4 > cc->cap * 3) {
    int newcap = cc->cap * 2;
    void *newdata = gc_alloc(gc, sizeof(void *) * stride * newcap, NULL, NULL, NULL);
    memset(newdata, 0, sizeof(void *) * stride * newcap);
    void **old = cc->data;
    void **nw = newdata;
    int mask = newcap - 1;
    for (int i = 0; i < cc->cap; i++) {
      int base = i * stride;
      if (old[base]) {
        int slot = cc_slot(cc_hash(&old[base], n), mask);
        while (nw[slot * stride]) slot = (slot + 1) & mask;
        memcpy(&nw[slot * stride], &old[base], sizeof(void *) * stride);
      }
    }
    cc->data = newdata;
    cc->cap = newcap;
  }
  void **arr = cc->data;
  int mask = cc->cap - 1;
  uint64_t h = cc_hash(args, n);
  for (int i = cc_slot(h, mask); ; i = (i + 1) & mask) {
    int base = i * stride;
    if (!arr[base]) {
      memcpy(&arr[base], args, sizeof(void *) * n);
      arr[base + n] = NULL;
      cc->count++;
      return &arr[base + n];
    }
    int match = 1;
    for (int j = 0; j < n; j++)
      if (arr[base + j] != args[j]) { match = 0; break; }
    if (match) return &arr[base + n];
  }
}

void gc_cc_clear(GCCallCache *cc) {
  if (cc->data) {
    memset(cc->data, 0, sizeof(void *) * (cc->nargs + 1) * cc->cap);
    cc->count = 0;
  }
}

int gc_cc_count(GCCallCache *cc) {
  return cc->count;
}

/* growable stack */

struct GCStack {
  void *data;
  int len;
  int cap;
};

static void gc_stack_trace(void *d) {
  GCStack *s = d;
  gc_mark(s->data);
  void **arr = s->data;
  for (int i = 0; i < s->len; i++)
    gc_mark(arr[i]);
}

void gc_stack_new(GC *gc, void **slot) {
  GCStack *s = gc_alloc(gc, sizeof(GCStack), gc_stack_trace, NULL, NULL);
  s->data = NULL;
  s->len = 0;
  s->cap = 16;
  *slot = s;
  s->data = gc_alloc(gc, sizeof(void *) * 16, NULL, NULL, NULL);
}

void **gc_stack_push(GC *gc, GCStack *s) {
  if (s->len >= s->cap) {
    int newcap = s->cap * 2;
    void *newdata = gc_alloc(gc, sizeof(void *) * newcap, NULL, NULL, NULL);
    memcpy(newdata, s->data, sizeof(void *) * s->len);
    s->data = newdata;
    s->cap = newcap;
  }
  void **arr = s->data;
  arr[s->len] = NULL;
  return &arr[s->len++];
}

void gc_stack_pop(GCStack *s, int n) {
  s->len -= n;
  if (s->cap > 16 && s->len <= s->cap / 4) {
    s->cap /= 2;
    /* data shrinks on next push via gc_alloc; for now just update cap */
  }
}

int gc_stack_len(GCStack *s) {
  return s->len;
}

void **gc_stack_nth(GCStack *s, int i) {
  return &((void **)s->data)[i];
}

void **gc_stack_top(GCStack *s) {
  return &((void **)s->data)[s->len - 1];
}
