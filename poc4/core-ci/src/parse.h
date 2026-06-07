#ifndef PARSE_H
#define PARSE_H

#include "node.h"

typedef struct Source Source;
typedef struct SourceMap SourceMap;

void source_map_new(GC *gc, void **slot);
typedef char *(*ReadFileFn)(const char *path);
Source *source_map_parse(GC *gc, SourceMap *sm, const char *filepath, ReadFileFn read_file);

#endif
