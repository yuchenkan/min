#include "intern.h"
#include "htable.h"
#include <assert.h>
#include <stdlib.h>
#include <string.h>

#define MIN_CAP 64

static int ptr_eq(const void *a, const void *b) { return a == b; }
static uint64_t ptr_hash(const void *p) { return (uintptr_t)p; }

/* --- string intern table --- */

static uint64_t str_hash(const void *p) {
  const char *s = p;
  uint64_t h = 14695981039346656037ULL;
  while (*s) { h ^= (unsigned char)*s++; h *= 1099511628211ULL; }
  return h;
}

static int str_eq(const void *a, const void *b) { return strcmp(a, b) == 0; }

/* --- array intern table --- */

typedef struct {
  uint64_t len;
  Node **elems;
  uint64_t hash;
} ArrKey;

typedef struct {
  Intern *intern;
  ArrKey *key;
} ArrFreeCtx;

static uint64_t arr_compute_hash(Node **elems, uint64_t len) {
  uint64_t h = len;
  for (uint64_t i = 0; i < len; i++)
    h = h * 0x9e3779b97f4a7c15ULL + (uintptr_t)elems[i];
  return h;
}

static uint64_t arrkey_hash(const void *p) {
  return ((const ArrKey *)p)->hash;
}

static int arrkey_eq(const void *a, const void *b) {
  const ArrKey *ka = a, *kb = b;
  if (ka->len != kb->len || ka->hash != kb->hash) return 0;
  for (uint64_t i = 0; i < ka->len; i++)
    if (ka->elems[i] != kb->elems[i]) return 0;
  return 1;
}

/* --- resize helpers --- */

static void ht_resize_malloc(HTable *t, int newcap, uint64_t (*hash_fn)(const void *)) {
  HTable fresh = { .entries = calloc(newcap, sizeof(HTEntry)), .cap = newcap, .count = 0, .ghost = 0 };
  ht_rehash(&fresh, t, hash_fn);
  free(t->entries);
  *t = fresh;
}

static void ht_maybe_resize(HTable *t, uint64_t (*hash_fn)(const void *)) {
  if (ht_needs_grow(t))
    ht_resize_malloc(t, t->cap * 2, hash_fn);
  else if (ht_needs_shrink(t, MIN_CAP))
    ht_resize_malloc(t, t->cap / 2, hash_fn);
}

/* --- Intern struct --- */

struct Intern {
  GC *gc;
  HTable tree;
  HTable ints;
  HTable strs;
  HTable arrs;
  Node *n_true;
  Node *n_false;
  Node *n_none;
};

static void ht_init_malloc(HTable *t, int cap) {
  t->entries = calloc(cap, sizeof(HTEntry));
  t->cap = cap;
  t->count = 0;
  t->ghost = 0;
}

Intern *intern_init(GC *gc) {
  Intern *t = malloc(sizeof(Intern));
  t->gc = gc;
  ht_init_malloc(&t->tree, MIN_CAP);
  ht_init_malloc(&t->ints, MIN_CAP);
  ht_init_malloc(&t->strs, MIN_CAP);
  ht_init_malloc(&t->arrs, MIN_CAP);
  t->n_true = NULL;
  t->n_false = NULL;
  t->n_none = NULL;
  return t;
}

void intern_fini(Intern *t) {
  assert(t->tree.count == 0);
  assert(t->ints.count == 0);
  assert(t->strs.count == 0);
  assert(t->arrs.count == 0);
  free(t->tree.entries);
  free(t->ints.entries);
  free(t->strs.entries);
  free(t->arrs.entries);
  free(t);
}

/* --- string intern --- */

static void t_free(void *data, void *ctx) {
  ht_del(&((Intern *)ctx)->tree, str_hash(data), data, str_eq);
  ht_maybe_resize(&((Intern *)ctx)->tree, str_hash);
}

const char *intern(Intern *t, const char *s) {
  uint64_t h = str_hash(s);
  void **d = ht_find(&t->tree, h, s, str_eq);
  if (d) return *d;
  ht_maybe_resize(&t->tree, str_hash);
  size_t len = strlen(s) + 1;
  char *copy = gc_alloc(t->gc, len, NULL, t_free, t);
  memcpy(copy, s, len);
  d = ht_get(&t->tree, h, copy, str_eq);
  *d = copy;
  return copy;
}

/* --- int intern --- */

static void int_free(void *data, void *ctx) {
  Node *n = data;
  void *key = (void *)(uintptr_t)(n->integer + 2);
  ht_del(&((Intern *)ctx)->ints, (uintptr_t)key, key, ptr_eq);
  ht_maybe_resize(&((Intern *)ctx)->ints, ptr_hash);
}

Node *intern_int(Intern *t, uint64_t val) {
  void *key = (void *)(uintptr_t)(val + 2);
  void **d = ht_find(&t->ints, (uintptr_t)key, key, ptr_eq);
  if (d) return *d;
  ht_maybe_resize(&t->ints, ptr_hash);
  Node *n = gc_alloc(t->gc, sizeof(Node), node_trace, int_free, t);
  memset(n, 0, sizeof(Node));
  n->tag = N_INT;
  n->integer = val;
  d = ht_get(&t->ints, (uintptr_t)key, key, ptr_eq);
  *d = n;
  return n;
}

/* --- str node intern --- */

static void str_node_free(void *data, void *ctx) {
  Node *n = data;
  ht_del(&((Intern *)ctx)->strs, (uintptr_t)n->str, n->str, ptr_eq);
  ht_maybe_resize(&((Intern *)ctx)->strs, ptr_hash);
}

Node *intern_str(Intern *t, const char *s) {
  void **d = ht_find(&t->strs, (uintptr_t)s, s, ptr_eq);
  if (d) return *d;
  ht_maybe_resize(&t->strs, ptr_hash);
  Node *n = gc_alloc(t->gc, sizeof(Node), node_trace, str_node_free, t);
  memset(n, 0, sizeof(Node));
  n->tag = N_STR;
  n->str = (char *)s;
  d = ht_get(&t->strs, (uintptr_t)s, (void *)s, ptr_eq);
  *d = n;
  return n;
}

/* --- arr intern --- */

static void arr_free(void *data, void *ctx) {
  (void)data;
  ArrFreeCtx *fc = ctx;
  ArrKey *key = fc->key;
  ht_del(&fc->intern->arrs, key->hash, key, arrkey_eq);
  ht_maybe_resize(&fc->intern->arrs, arrkey_hash);
  free(key->elems);
  free(key);
  free(fc);
}

void intern_arr(Intern *t, Node **elems, uint64_t len, void **slot) {
  uint64_t h = arr_compute_hash(elems, len);
  ArrKey lookup = { len, elems, h };
  void **d = ht_find(&t->arrs, h, &lookup, arrkey_eq);
  if (d) { *slot = *d; return; }

  ht_maybe_resize(&t->arrs, arrkey_hash);

  ArrKey *key = malloc(sizeof(ArrKey));
  key->len = len;
  key->hash = h;
  key->elems = malloc(sizeof(Node *) * (len > 0 ? len : 1));
  if (len > 0) memcpy(key->elems, elems, sizeof(Node *) * len);

  ArrFreeCtx *fc = malloc(sizeof(ArrFreeCtx));
  fc->intern = t;
  fc->key = key;

  Node *n = gc_alloc(t->gc, sizeof(Node), node_trace, arr_free, fc);
  memset(n, 0, sizeof(Node));
  n->tag = N_ARR;
  *slot = n;
  if (len > 0) {
    n->arr.data = gc_alloc(t->gc, sizeof(Node *) * len, NULL, NULL, NULL);
    memcpy(n->arr.data, elems, sizeof(Node *) * len);
  }
  n->arr.len = len;

  d = ht_get(&t->arrs, h, key, arrkey_eq);
  *d = n;
}

/* --- singletons --- */

static Node *singleton(GC *gc, Node **cache, int tag) {
  if (!*cache) {
    *cache = gc_alloc(gc, sizeof(Node), NULL, NULL, NULL);
    memset(*cache, 0, sizeof(Node));
    (*cache)->tag = tag;
  }
  return *cache;
}

Node *intern_true(Intern *t)  { return singleton(t->gc, &t->n_true, N_TRUE); }
Node *intern_false(Intern *t) { return singleton(t->gc, &t->n_false, N_FALSE); }
Node *intern_none(Intern *t)  { return singleton(t->gc, &t->n_none, N_NONE); }
