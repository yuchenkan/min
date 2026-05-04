"""Goal: what the agent should prove. Run this file to test."""

import sys
sys.setrecursionlimit(100000)
sys.path.insert(0, 'src')

from core.lang import Var, Forall, Implies
from core.derived import Exists, Eq, And
from core.proof import qed, same
from core.zfc import ZFCAxiom
from definitions import OrdPair

is_axiom = lambda f: isinstance(f, ZFCAxiom)

import theorems

# --- Goals ---

x, y, p = Var(), Var(), Var()
a, b, c, d, t = Var(), Var(), Var(), Var(), Var()

# tuple_injection: OrdPair(t,a,b) -> OrdPair(t,c,d) -> And(Eq(a,c), Eq(b,d))
ti_goal = Forall(a, Forall(b, Forall(c, Forall(d, Forall(t,
    Implies(OrdPair(t, a, b), Implies(OrdPair(t, c, d), And(Eq(a, c), Eq(b, d)))))))))

# ordpair_exists: Pairing |- forall x, y. exists p. OrdPair(p, x, y)
oe_goal = Forall(x, Forall(y, Exists(p, OrdPair(p, x, y))))

goals = [
    ('tuple_injection', theorems.tuple_injection, ti_goal),
]

if __name__ == '__main__':
    for name, build, expected in goals:
        print(f'{name}: {expected}')
        try:
            proof = build()
            assert same(proof.sequent.right[0], expected, expand=False), \
                f'wrong theorem: {proof.sequent.right[0]}'
            assert qed(proof, is_axiom), 'qed failed'
            print(f'{name}: ok')
        except Exception as e:
            print(f'{name}: {e}')
