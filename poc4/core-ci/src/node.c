#include "node.h"
#include <assert.h>
#include <string.h>

void node_trace(void *data) {
  Node *n = data;
  gc_mark((void *)n->file);
  switch (n->tag) {
  case N_INT: break;
  case N_STR: gc_mark(n->str); break;
  case N_LIST: gc_mark(n->list); break;
  case N_REF: gc_mark(n->ref); break;
  case N_FN:
    gc_mark(n->fn.params);
    gc_mark(n->fn.body);
    break;
  case N_CALL:
    gc_mark(n->call.callee);
    gc_mark(n->call.args);
    break;
  case N_IF:
    gc_mark(n->if_.cond);
    gc_mark(n->if_.then);
    gc_mark(n->if_.else_);
    break;
  case N_BLOCK:
    gc_mark(n->block.binds);
    gc_mark(n->block.expr);
    break;
  case N_BIND:
    gc_mark(n->bind.name);
    gc_mark(n->bind.expr);
    break;
  case N_IMPORT:
    gc_mark(n->import.filepath);
    gc_mark(n->import.names);
    break;
  case N_ARR:
    gc_mark(n->arr.data);
    for (uint64_t i = 0; i < n->arr.len; i++)
      gc_mark(((Node **)n->arr.data)[i]);
    break;
  case N_CLOSURE:
    gc_mark(n->closure.params);
    gc_mark(n->closure.body);
    gc_mark(n->closure.env);
    gc_mark(n->closure.cache);
    break;
  case N_BUILTIN:
    gc_mark(n->builtin.cache);
    gc_mark(n->builtin.ctx);
    break;
  case N_PROOF:
    gc_mark(n->proof.left);
    gc_mark(n->proof.right);
    break;
  }
}

void node_new(GC *gc, void **slot, int tag) {
  assert(tag != N_INT && tag != N_STR && tag != N_ARR && tag != N_TRUE && tag != N_FALSE && tag != N_NONE);
  Node *n = gc_alloc(gc, sizeof(Node), node_trace, NULL, NULL);
  memset(n, 0, sizeof(Node));
  n->tag = tag;
  *slot = n;
}

static void env_trace(void *data) {
  Env *e = data;
  gc_mark(e->map);
  gc_mark(e->parent);
}

void env_new(GC *gc, void **slot) {
  Env *e = gc_alloc(gc, sizeof(Env), env_trace, NULL, NULL);
  e->parent = NULL;
  e->map = NULL;
  *slot = e;
  e->map = gc_map_new(gc);
}

Node **env_get(GC *gc, Env *e, const char *name) {
  return (Node **)gc_map_get(gc, e->map, name);
}

Node **env_find(Env *e, const char *name) {
  while (e) {
    void **slot = gc_map_find(e->map, name);
    if (slot) return (Node **)slot;
    e = e->parent;
  }
  return NULL;
}

void module_trace(void *data) {
  Module *m = data;
  gc_mark(m->env);
  gc_mark(m->imports);
}
