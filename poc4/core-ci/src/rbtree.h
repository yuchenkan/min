#ifndef RBTREE_H
#define RBTREE_H

typedef struct RBNode {
  const void *key;
  void *val;
  struct RBNode *left;
  struct RBNode *right;
  int color;
} RBNode;

typedef int (*RBCmpFn)(const void *a, const void *b);
typedef RBNode *(*RBAllocFn)(void *ctx);
typedef void (*RBFreeFn)(RBNode *node, void *ctx);

typedef struct RBTree {
  RBNode *root;
  RBCmpFn cmp;
  RBAllocFn alloc;
  RBFreeFn free_fn;
  void *ctx;
} RBTree;

void rb_init(RBTree *t, RBCmpFn cmp, RBAllocFn alloc, RBFreeFn free_fn, void *ctx);
void **rb_get(RBTree *t, const void *key);
void **rb_find(RBTree *t, const void *key);
void rb_delete(RBTree *t, const void *key);
void rb_copy(RBTree *dst, RBTree *src);
#endif
