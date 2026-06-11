#ifndef EVAL_H
#define EVAL_H

#include "node.h"
#include "parse.h"

void init_global(GC *gc, GCStack *stack, const char **tags, Intern *it, Env *global, void **slot);
int eval(GC *gc, GCMap *modules, GCMap *sources, const char *filepath, Env *global, GCStack *stack, const char **tags, Intern *it, Env **out);

#endif
