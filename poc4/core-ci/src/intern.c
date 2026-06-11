#include "intern.h"
#include "rbtree.h"
#include <assert.h>
#include <stdlib.h>
#include <string.h>

static int ptr_cmp(const void *a, const void *b) {
  return (a > b) - (a < b);
}

typedef struct {
  uint64_t len;
  Node **elems;
} ArrKey;

typedef struct {
  Intern *intern;
  ArrKey *key;
} ArrFreeCtx;

static int arr_cmp(const void *a, const void *b) {
  const ArrKey *ka = a, *kb = b;
  if (ka->len != kb->len)
    return (ka->len > kb->len) - (ka->len < kb->len);
  for (uint64_t i = 0; i < ka->len; i++) {
    if (ka->elems[i] != kb->elems[i])
      return ((uintptr_t)ka->elems[i] > (uintptr_t)kb->elems[i])
           - ((uintptr_t)ka->elems[i] < (uintptr_t)kb->elems[i]);
  }
  return 0;
}

struct Intern {
  GC *gc;
  RBTree tree;
  RBTree ints;
  RBTree strs;
  RBTree arrs;
  Node *n_true;
  Node *n_false;
  Node *n_none;
};

static RBNode *m_alloc(void *ctx) { (void)ctx; return malloc(sizeof(RBNode)); }
static void m_free(RBNode *n, void *ctx) { (void)ctx; free(n); }

Intern *intern_init(GC *gc) {
  Intern *t = malloc(sizeof(Intern));
  t->gc = gc;
  rb_init(&t->tree, (RBCmpFn)strcmp, m_alloc, m_free, NULL);
  rb_init(&t->ints, ptr_cmp, m_alloc, m_free, NULL);
  rb_init(&t->strs, ptr_cmp, m_alloc, m_free, NULL);
  rb_init(&t->arrs, arr_cmp, m_alloc, m_free, NULL);
  t->n_true = NULL;
  t->n_false = NULL;
  t->n_none = NULL;
  return t;
}

void intern_fini(Intern *t) {
  assert(!t->tree.root);
  assert(!t->ints.root);
  assert(!t->strs.root);
  assert(!t->arrs.root);
  free(t);
}

static void t_free(void *data, void *ctx) {
  rb_delete(&((Intern *)ctx)->tree, data);
}

const char *intern(Intern *t, const char *s) {
  void **d = rb_find(&t->tree, s);
  if (d) return *d;
  size_t len = strlen(s) + 1;
  char *copy = gc_alloc(t->gc, len, NULL, t_free, t);
  memcpy(copy, s, len);
  d = rb_get(&t->tree, copy);
  *d = copy;
  return copy;
}

static void int_free(void *data, void *ctx) {
  Node *n = data;
  rb_delete(&((Intern *)ctx)->ints, (void *)(uintptr_t)n->integer);
}

Node *intern_int(Intern *t, uint64_t val) {
  void *key = (void *)(uintptr_t)val;
  void **d = rb_find(&t->ints, key);
  if (d) return *d;
  Node *n = gc_alloc(t->gc, sizeof(Node), node_trace, int_free, t);
  memset(n, 0, sizeof(Node));
  n->tag = N_INT;
  n->integer = val;
  d = rb_get(&t->ints, key);
  *d = n;
  return n;
}

static void str_free(void *data, void *ctx) {
  Node *n = data;
  rb_delete(&((Intern *)ctx)->strs, n->str);
}

Node *intern_str(Intern *t, const char *s) {
  void **d = rb_find(&t->strs, s);
  if (d) return *d;
  Node *n = gc_alloc(t->gc, sizeof(Node), node_trace, str_free, t);
  memset(n, 0, sizeof(Node));
  n->tag = N_STR;
  n->str = (char *)s;
  d = rb_get(&t->strs, (void *)s);
  *d = n;
  return n;
}

static void arr_free(void *data, void *ctx) {
  (void)data;
  ArrFreeCtx *fc = ctx;
  rb_delete(&fc->intern->arrs, fc->key);
  free(fc->key->elems);
  free(fc->key);
  free(fc);
}

void intern_arr(Intern *t, Node **elems, uint64_t len, void **slot) {
  ArrKey lookup = { len, elems };
  void **d = rb_find(&t->arrs, &lookup);
  if (d) { *slot = *d; return; }

  ArrKey *key = malloc(sizeof(ArrKey));
  key->len = len;
  key->elems = malloc(sizeof(Node *) * len);
  memcpy(key->elems, elems, sizeof(Node *) * len);

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

  d = rb_get(&t->arrs, key);
  *d = n;
}

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
