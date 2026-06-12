#ifndef PARSE_H
#define PARSE_H

#include "node.h"
#include "intern.h"
#include <stdint.h>

typedef struct Source {
  GCList *imports;
  GCList *binds;
  int loading;
  int64_t mtime;
} Source;

typedef char *(*ReadFileFn)(const char *path, int64_t *mtime);

int parse(GC *gc, Intern *intern_t, GCMap *sources, GCMap *modules, const char *filepath, ReadFileFn read_file);

#endif
