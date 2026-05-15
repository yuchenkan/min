"""Test tm_add_correct: chain Phase1P..Phase5P into TMReaches(delta,c0,n,cf)."""
import sys
sys.setrecursionlimit(100000)
sys.path.insert(0, 'src')

from core.lang import Var, In, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq
from core.proof import qed, same
from core.zfc import ZFCAxiom
from theorems.tm import Phase1P, Phase2P, Phase3P, Phase4P, Phase5P

is_axiom = lambda f: isinstance(f, (ZFCAxiom, Phase1P, Phase2P, Phase3P, Phase4P, Phase5P))

def test():
    from theorems.tm import tm_add_correct
    proof = tm_add_correct()
    assert qed(proof, is_axiom), 'qed failed'
    print('tm_add_correct VERIFIED')

if __name__ == '__main__':
    test()
