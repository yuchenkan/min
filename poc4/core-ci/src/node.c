#include "node.h"
#include <string.h>

static void node_trace(void *data) {
  Node *n = data;
  switch (n->tag) {
  case N_INT: gc_mark(n->integer.limbs); break;
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
  }
}

Node *node_new(GC *gc, int tag) {
  Node *n = gc_alloc(gc, sizeof(Node), node_trace);
  memset(n, 0, sizeof(Node));
  n->tag = tag;
  return n;
}
