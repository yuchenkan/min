#ifndef CACHE_H
#define CACHE_H

#include "parse.h"
#include <stddef.h>

typedef struct {
  void *(*fopen)(const char *path, const char *mode);
  int (*fclose)(void *f);
  size_t (*fread)(void *buf, size_t size, size_t count, void *f);
  size_t (*fwrite)(const void *buf, size_t size, size_t count, void *f);
  int (*fseek)(void *f, long offset, int whence);
  int64_t (*mtime)(const char *path);
} CacheOps;

int cache_save(const char *path, GC *gc, GCMap *modules, Env *global, CacheOps *ops);
int cache_load(const char *path, GC *gc, Intern *it, GCMap *modules, Env *global, void **slot, CacheOps *ops);

#endif
