"""Goal: what the agent should prove. Run this file to test."""

import sys
sys.setrecursionlimit(100000)
sys.path.insert(0, 'src')

from core.lang import Var, Forall
from core.derived import Exists
from core.proof import qed, same
from core.zfc import ZFCAxiom
from definitions import OrdPair

is_axiom = lambda f: isinstance(f, ZFCAxiom)

# Expected: Pairing |- forall x, y. exists p. OrdPair(p, x, y)
x, y, p = Var(), Var(), Var()
ordpair_goal = Forall(x, Forall(y, Exists(p, OrdPair(p, x, y))))

import theorems

goals = [
    ('ordpair_exists', theorems.ordpair_exists, ordpair_goal),
]

if __name__ == '__main__':
    for name, build, expected in goals:
        print(f'{name}: proving {expected}')
        try:
            proof = build()
            assert same(proof.sequent.right[0], expected, expand=False), \
                f'wrong theorem: {proof.sequent.right[0]}'
            assert qed(proof, is_axiom), 'qed failed'
            print(f'{name}: ok')
        except Exception as e:
            print(f'{name}: {e}')
