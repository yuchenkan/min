#include "intern.h"
#include "rbtree.h"
#include <assert.h>
#include <stdlib.h>
#include <string.h>

struct Intern {
  GC *gc;
  RBTree tree;
};

static RBNode *m_alloc(void *ctx) { (void)ctx; return malloc(sizeof(RBNode)); }
static void m_free(RBNode *n, void *ctx) { (void)ctx; free(n); }

Intern *intern_init(GC *gc) {
  Intern *t = malloc(sizeof(Intern));
  t->gc = gc;
  rb_init(&t->tree, (RBCmpFn)strcmp, m_alloc, m_free, NULL);
  return t;
}

void intern_fini(Intern *t) {
  assert(!t->tree.root);
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
