#ifndef PARSE_H
#define PARSE_H

#include "node.h"
#include "intern.h"

typedef struct Source {
  GCList *imports;
  GCList *binds;
  int loading;
} Source;
typedef char *(*ReadFileFn)(const char *path);

void parse(GC *gc, Intern *intern_t, GCMap *sources, const char *filepath, ReadFileFn read_file);

#endif
