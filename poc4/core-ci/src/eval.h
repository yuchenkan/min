#ifndef EVAL_H
#define EVAL_H

#include "node.h"
#include "parse.h"

void init_global(GC *gc, GCStack *stack, const char **tags, Intern *it, Node *global, void **slot);
Node *eval(GC *gc, GCMap *modules, GCMap *sources, const char *filepath, Node *global, GCStack *stack, const char **tags, Intern *it);

#endif
