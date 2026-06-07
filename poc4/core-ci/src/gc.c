#include "gc.h"
#include <stdlib.h>
#include <string.h>

typedef struct GCObject GCObject;

struct GCObject {
  GCObject *prev;
  GCObject *next;
  GCTraceFn trace;
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
  void *root = gc_alloc(gc, root_size, root_trace);
  gc->root = data_obj(root);
  *out = gc;
  return root;
}

void gc_fini(GC *gc) {
  GCObject *obj = gc->sentinel.next;
  while (obj != &gc->sentinel) {
    GCObject *next = obj->next;
    free(obj);
    obj = next;
  }
  free(gc);
}

void *gc_alloc(GC *gc, size_t size, GCTraceFn trace_fn) {
  if (gc->root && gc->total >= gc->threshold) {
    gc_mark(obj_data(gc->root));
    gc_sweep(gc);
  }
  GCObject *obj = malloc(sizeof(GCObject) + size);
  obj->trace = trace_fn;
  obj->size = sizeof(GCObject) + size;
  obj->mark = 0;
  gc_link(gc, obj);
  gc->total += obj->size;
  return obj_data(obj);
}

char *gc_strdup(GC *gc, const char *s) {
  size_t len = strlen(s) + 1;
  char *p = gc_alloc(gc, len, NULL);
  memcpy(p, s, len);
  return p;
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
  GCList *list = gc_alloc(gc, sizeof(GCList), gc_list_trace);
  list->head = NULL;
  list->tail = &list->head;
  return list;
}

void **gc_list_append(GC *gc, GCList *list) {
  GCListNode *node = gc_alloc(gc, sizeof(GCListNode), gc_list_node_trace);
  node->item = NULL;
  node->next = NULL;
  *list->tail = node;
  list->tail = &node->next;
  return &node->item;
}

void gc_list_each(GCList *list, GCListFn fn, void *ctx) {
  for (GCListNode *node = list->head; node; node = node->next)
    fn(node->item, ctx);
}

/* string-to-void* red-black tree map */

enum { RB_BLACK, RB_RED };

typedef struct GCMapNode GCMapNode;

struct GCMapNode {
  const char *key;
  void *val;
  GCMapNode *left;
  GCMapNode *right;
  int color;
};

struct GCMap {
  GCMapNode *root;
};

static void gc_map_node_trace(void *data) {
  GCMapNode *n = data;
  gc_mark((void *)n->key);
  gc_mark(n->val);
  gc_mark(n->left);
  gc_mark(n->right);
}

static void gc_map_trace(void *data) {
  GCMap *m = data;
  gc_mark(m->root);
}

static int rb_is_red(GCMapNode *n) {
  return n && n->color == RB_RED;
}

static GCMapNode *rb_rotate_left(GCMapNode *h) {
  GCMapNode *x = h->right;
  h->right = x->left;
  x->left = h;
  x->color = h->color;
  h->color = RB_RED;
  return x;
}

static GCMapNode *rb_rotate_right(GCMapNode *h) {
  GCMapNode *x = h->left;
  h->left = x->right;
  x->right = h;
  x->color = h->color;
  h->color = RB_RED;
  return x;
}

static void rb_flip_colors(GCMapNode *h) {
  h->color = RB_RED;
  h->left->color = RB_BLACK;
  h->right->color = RB_BLACK;
}

static GCMapNode *rb_insert(GC *gc, GCMapNode *h, const char *key, void ***out) {
  if (!h) {
    GCMapNode *n = gc_alloc(gc, sizeof(GCMapNode), gc_map_node_trace);
    n->key = key;
    n->val = NULL;
    n->left = NULL;
    n->right = NULL;
    n->color = RB_RED;
    *out = &n->val;
    return n;
  }
  int cmp = strcmp(key, h->key);
  if (cmp < 0)
    h->left = rb_insert(gc, h->left, key, out);
  else if (cmp > 0)
    h->right = rb_insert(gc, h->right, key, out);
  else *out = &h->val;

  if (rb_is_red(h->right) && !rb_is_red(h->left))
    h = rb_rotate_left(h);
  if (rb_is_red(h->left) && rb_is_red(h->left->left))
    h = rb_rotate_right(h);
  if (rb_is_red(h->left) && rb_is_red(h->right))
    rb_flip_colors(h);
  return h;
}

GCMap *gc_map_new(GC *gc) {
  GCMap *m = gc_alloc(gc, sizeof(GCMap), gc_map_trace);
  m->root = NULL;
  return m;
}

void **gc_map_get(GC *gc, GCMap *map, const char *key) {
  void **out;
  map->root = rb_insert(gc, map->root, key, &out);
  map->root->color = RB_BLACK;
  return out;
}
