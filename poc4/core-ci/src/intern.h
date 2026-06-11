#ifndef INTERN_H
#define INTERN_H

#include "gc.h"

typedef struct Intern Intern;

Intern *intern_init(GC *gc);
void intern_fini(Intern* t);

const char *intern(Intern *t, const char *s);

#endif
