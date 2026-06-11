#ifndef INTERN_H
#define INTERN_H

#include "gc.h"
#include "node.h"

typedef struct Intern Intern;

Intern *intern_init(GC *gc);
void intern_fini(Intern* t);

const char *intern(Intern *t, const char *s);
Node *intern_int(Intern *t, uint64_t val);
Node *intern_str(Intern *t, const char *s);
void intern_arr(Intern *t, Node **elems, uint64_t len, void **slot);
Node *intern_true(Intern *t);
Node *intern_false(Intern *t);
Node *intern_none(Intern *t);

#endif
