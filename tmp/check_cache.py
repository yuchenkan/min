"""Run all goals with functools.cache to verify caching doesn't break anything."""
import sys
sys.setrecursionlimit(100000)
sys.path.insert(0, 'src')

import functools, inspect
import theorems.logic, theorems.sets, theorems.omega, theorems.recursion, theorems.arithmetic, theorems.tm
import theorems

modules = [theorems.logic, theorems.sets, theorems.omega, theorems.recursion, theorems.arithmetic, theorems.tm]
cached_count = 0
for mod in modules:
    for name in dir(mod):
        fn = getattr(mod, name)
        if callable(fn) and not name.startswith('_') and not inspect.isclass(fn):
            try:
                sig = inspect.signature(fn)
                if len(sig.parameters) == 0:
                    cached = functools.cache(fn)
                    setattr(mod, name, cached)
                    if hasattr(theorems, name):
                        setattr(theorems, name, cached)
                    cached_count += 1
            except (ValueError, TypeError):
                pass

print(f"Cached {cached_count} parameterless theorems")

# Now run goal.py
exec(open('goal.py').read())
