#ifndef VAL_H
#define VAL_H

#include "gc.h"
#include <stdbool.h>
#include <stdint.h>

typedef struct Val Val;
typedef struct Env Env;
typedef Val *(*BuiltinFn)(Val **args, int nargs);

/* singletons */
extern Val *val_nil;
extern Val *val_true;
extern Val *val_false;

void val_init(void);

/* constructors — returned Val has refcount 1 */
Val *val_int(const uint32_t *limbs, int len);
Val *val_str(const char *s);
Val *val_list(Val **items, int len);
Val *val_fn(const char **params, int nparams, Val *body, Env *env);
Val *val_builtin(BuiltinFn fn, const char *name, bool nocache);

/* environment */
Env *env_new(void);
Env *env_snapshot(Env *e);
void env_set(Env *e, const char *name, Val *val);
Val *env_get(Env *e, const char *name);

#endif
