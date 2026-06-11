#include "rbtree.h"
#include <stddef.h>

enum { RB_BLACK, RB_RED };

static int is_red(RBNode *n) {
  return n && n->color == RB_RED;
}

static RBNode *rotate_left(RBNode *h) {
  RBNode *x = h->right;
  h->right = x->left;
  x->left = h;
  x->color = h->color;
  h->color = RB_RED;
  return x;
}

static RBNode *rotate_right(RBNode *h) {
  RBNode *x = h->left;
  h->left = x->right;
  x->right = h;
  x->color = h->color;
  h->color = RB_RED;
  return x;
}

static void flip_colors(RBNode *h) {
  h->color = RB_RED;
  h->left->color = RB_BLACK;
  h->right->color = RB_BLACK;
}

static RBNode *do_insert(RBNode *h, const void *key, void ***out, RBTree *t) {
  if (!h) {
    RBNode *n = t->alloc(t->ctx);
    n->key = key;
    n->val = NULL;
    n->left = NULL;
    n->right = NULL;
    n->color = RB_RED;
    *out = &n->val;
    return n;
  }
  int c = t->cmp(key, h->key);
  if (c < 0)
    h->left = do_insert(h->left, key, out, t);
  else if (c > 0)
    h->right = do_insert(h->right, key, out, t);
  else
    *out = &h->val;

  if (is_red(h->right) && !is_red(h->left))
    h = rotate_left(h);
  if (is_red(h->left) && is_red(h->left->left))
    h = rotate_right(h);
  if (is_red(h->left) && is_red(h->right))
    flip_colors(h);
  return h;
}

void rb_init(RBTree *t, RBCmpFn cmp, RBAllocFn alloc, RBFreeFn free_fn, void *ctx) {
  t->root = NULL;
  t->cmp = cmp;
  t->alloc = alloc;
  t->free_fn = free_fn;
  t->ctx = ctx;
}

void **rb_get(RBTree *t, const void *key) {
  void **out;
  t->root = do_insert(t->root, key, &out, t);
  t->root->color = RB_BLACK;
  return out;
}

void **rb_find(RBTree *t, const void *key) {
  RBNode *n = t->root;
  while (n) {
    int c = t->cmp(key, n->key);
    if (c < 0) n = n->left;
    else if (c > 0) n = n->right;
    else return &n->val;
  }
  return NULL;
}

static void flip_colors_del(RBNode *h) {
  h->color = !h->color;
  if (h->left) h->left->color = !h->left->color;
  if (h->right) h->right->color = !h->right->color;
}

static RBNode *fix_up(RBNode *h) {
  if (is_red(h->right) && !is_red(h->left))
    h = rotate_left(h);
  if (is_red(h->left) && is_red(h->left->left))
    h = rotate_right(h);
  if (is_red(h->left) && is_red(h->right))
    flip_colors_del(h);
  return h;
}

static RBNode *move_red_left(RBNode *h) {
  flip_colors_del(h);
  if (h->right && is_red(h->right->left)) {
    h->right = rotate_right(h->right);
    h = rotate_left(h);
    flip_colors_del(h);
  }
  return h;
}

static RBNode *move_red_right(RBNode *h) {
  flip_colors_del(h);
  if (h->left && is_red(h->left->left)) {
    h = rotate_right(h);
    flip_colors_del(h);
  }
  return h;
}

static RBNode *node_min(RBNode *h) {
  while (h->left) h = h->left;
  return h;
}

static RBNode *do_delete_min(RBNode *h, RBTree *t) {
  if (!h->left) { t->free_fn(h, t->ctx); return NULL; }
  if (!is_red(h->left) && !is_red(h->left->left))
    h = move_red_left(h);
  h->left = do_delete_min(h->left, t);
  return fix_up(h);
}

static RBNode *do_remove(RBNode *h, const void *key, RBTree *t) {
  if (!h) return NULL;
  if (t->cmp(key, h->key) < 0) {
    if (h->left && !is_red(h->left) && !is_red(h->left->left))
      h = move_red_left(h);
    h->left = do_remove(h->left, key, t);
  } else {
    if (is_red(h->left))
      h = rotate_right(h);
    if (t->cmp(key, h->key) == 0 && !h->right) {
      t->free_fn(h, t->ctx);
      return NULL;
    }
    if (h->right && !is_red(h->right) && !is_red(h->right->left))
      h = move_red_right(h);
    if (t->cmp(key, h->key) == 0) {
      RBNode *m = node_min(h->right);
      h->key = m->key;
      h->val = m->val;
      h->right = do_delete_min(h->right, t);
    } else {
      h->right = do_remove(h->right, key, t);
    }
  }
  return fix_up(h);
}

void rb_delete(RBTree *t, const void *key) {
  t->root = do_remove(t->root, key, t);
  if (t->root) t->root->color = RB_BLACK;
}

static void do_copy(RBNode **dst, RBNode *src, RBTree *t) {
  if (!src) return;
  RBNode *c = t->alloc(t->ctx);
  c->key = src->key;
  c->val = src->val;
  c->color = src->color;
  c->left = NULL;
  c->right = NULL;
  *dst = c;
  do_copy(&c->left, src->left, t);
  do_copy(&c->right, src->right, t);
}

void rb_copy(RBTree *dst, RBTree *src) {
  do_copy(&dst->root, src->root, dst);
}
