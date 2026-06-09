#ifndef KERNEL_H
#define KERNEL_H

#include "node.h"

const char *kernel_check(GC *gc, GCStack *stack,
                         Node *left, Node *right, const char *rule,
                         Node *premises, Node *principal, Node *term);

const char *kernel_qed(GC *gc, GCStack *stack,
                       Node *proof, Node *expected, const char *system);

#endif
