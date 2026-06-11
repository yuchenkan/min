#include "gc.h"
#include "rbtree.h"
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

void gc_list_each(GCList *list, GCListFn fn, void *ctx) {
  for (GCListNode *node = list->head; node; node = node->next)
    fn(node->item, ctx);
}

/* string-to-void* map backed by generic rbtree */

struct GCMap {
  RBTree tree;
};

static void rb_node_trace(void *data) {
  RBNode *n = data;
  gc_mark((void *)n->key);
  gc_mark(n->val);
  gc_mark(n->left);
  gc_mark(n->right);
}

static void gc_map_trace(void *data) {
  GCMap *m = data;
  gc_mark(m->tree.root);
}

static int gc_rb_cmp(const void *a, const void *b) {
  return (a > b) - (a < b);
}

static RBNode *gc_rb_alloc(void *ctx) {
  return gc_alloc(ctx, sizeof(RBNode), rb_node_trace, NULL, NULL);
}

static void gc_rb_nop(RBNode *node, void *ctx) {
  (void)node; (void)ctx;
}

GCMap *gc_map_new(GC *gc) {
  GCMap *m = gc_alloc(gc, sizeof(GCMap), gc_map_trace, NULL, NULL);
  rb_init(&m->tree, gc_rb_cmp, gc_rb_alloc, gc_rb_nop, gc);
  return m;
}

void **gc_map_get(GC *gc, GCMap *map, const char *key) {
  (void)gc;
  return rb_get(&map->tree, key);
}

void gc_map_delete(GCMap *map, const char *key) {
  rb_delete(&map->tree, key);
}

void **gc_map_find(GCMap *map, const char *key) {
  return rb_find(&map->tree, key);
}

void gc_map_copy(GC *gc, void **slot, GCMap *src) {
  GCMap *dst = gc_alloc(gc, sizeof(GCMap), gc_map_trace, NULL, NULL);
  rb_init(&dst->tree, gc_rb_cmp, gc_rb_alloc, gc_rb_nop, gc);
  *slot = dst;
  rb_copy(&dst->tree, &src->tree);
}

/* pointer-to-void* map */

struct GCNMap {
  RBTree tree;
};

static void gc_nmap_trace(void *data) {
  GCNMap *m = data;
  gc_mark(m->tree.root);
}

GCNMap *gc_nmap_new(GC *gc) {
  GCNMap *m = gc_alloc(gc, sizeof(GCNMap), gc_nmap_trace, NULL, NULL);
  rb_init(&m->tree, gc_rb_cmp, gc_rb_alloc, gc_rb_nop, gc);
  return m;
}

void **gc_nmap_get(GC *gc, GCNMap *map, void *key) {
  (void)gc;
  return rb_get(&map->tree, key);
}

void **gc_nmap_find(GCNMap *map, void *key) {
  return rb_find(&map->tree, key);
}

void gc_nmap_clear(GCNMap *map) {
  map->tree.root = NULL;
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
