"""Count Proof() constructions with DAG dedup via functools.cache."""
import sys
sys.setrecursionlimit(100000)
sys.path.insert(0, 'src')

from core.proof import Proof

proof_count = 0
rule_counts = {}
original_init = Proof.__init__

def counting_init(self, sequent, rule, premises=None, name=None, term=None, principal=None):
    global proof_count
    proof_count += 1
    rule_counts[rule] = rule_counts.get(rule, 0) + 1
    original_init(self, sequent, rule, premises, name, term, principal)

Proof.__init__ = counting_init

import functools, inspect
import theorems.logic, theorems.sets, theorems.omega, theorems.recursion, theorems.arithmetic, theorems.tm
import theorems

modules = [theorems.logic, theorems.sets, theorems.omega, theorems.recursion, theorems.arithmetic, theorems.tm]
cached_count = 0
seen_fns = set()
for mod in modules:
    for name in dir(mod):
        fn = getattr(mod, name)
        if callable(fn) and not name.startswith('_') and not inspect.isclass(fn):
            try:
                sig = inspect.signature(fn)
                if len(sig.parameters) == 0:
                    fn_id = f"{mod.__name__}.{name}"
                    orig_fn = fn
                    def make_wrapper(f, fid):
                        @functools.cache
                        def wrapper():
                            seen_fns.add(fid)
                            return f()
                        return wrapper
                    wrapped = make_wrapper(fn, fn_id)
                    setattr(mod, name, wrapped)
                    if hasattr(theorems, name):
                        setattr(theorems, name, wrapped)
                    cached_count += 1
            except (ValueError, TypeError):
                pass

print(f"Cached {cached_count} parameterless theorems")

goal_name = sys.argv[1] if len(sys.argv) > 1 else 'eq_reflexive'

build_fns = {
    'eq_reflexive': lambda: theorems.eq_reflexive(),
    'eq_symmetric': lambda: theorems.eq_symmetric(),
    'kuratowski': lambda: theorems.kuratowski(),
    'recursion_theorem': lambda: theorems.recursion_theorem(),
    'plus_comm': lambda: theorems.plus_comm(),
    'plus_assoc': lambda: theorems.plus_assoc(),
    'prove_2_plus_2': lambda: theorems.prove_addition(2, 2),
    'tm_add_correct': lambda: theorems.tm_add_correct(),
}

if goal_name not in build_fns:
    print(f"Available: {', '.join(build_fns.keys())}")
    sys.exit(1)

print(f"\nBuilding [cached DAG]: {goal_name}")
build_fns[goal_name]()
print(f"Proof steps: {proof_count}")
print(f"Unique parameterless theorems: {len(seen_fns)}")
print(f"Rules:")
for rule, count in sorted(rule_counts.items(), key=lambda x: -x[1]):
    print(f"  {rule}: {count}")
