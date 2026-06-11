#ifndef KERNEL_H
#define KERNEL_H

#include "node.h"

enum {
  K_MEM, K_NEG, K_IMPLIES, K_FORALL,
  K_AXIOM, K_NEG_LEFT, K_NEG_RIGHT,
  K_IMPLIES_LEFT, K_IMPLIES_RIGHT,
  K_FORALL_LEFT, K_FORALL_RIGHT,
  K_CUT, K_WEAKENING_LEFT, K_WEAKENING_RIGHT,
  K_Z, K_ZF, K_ZFC,
  K_A, K_B, K_X, K_Y, K_UNDERSCORE,
  K_W, K_C, K_E, K_S, K_UZ,
  K_COUNT
};

const char *kernel_check(GC *gc, GCStack *stack, const char **tags,
                         Node *left, Node *right, const char *rule,
                         Node *premises, Node *principal, Node *term);

const char *kernel_qed(GC *gc, GCStack *stack, const char **tags,
                       Node *proof, Node *expected, const char *system);

#endif
