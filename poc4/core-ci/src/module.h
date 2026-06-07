#ifndef MODULE_H
#define MODULE_H

#include "node.h"

typedef struct Module Module;
typedef struct ModuleMap ModuleMap;

void module_map_new(GC *gc, void **slot);
Module *module_map_parse(GC *gc, ModuleMap *mm, const char *filepath);

#endif
