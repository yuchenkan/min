"""Test tm_add_correct: chain Phase1P..Phase5P into TMReaches(delta,c0,n,cf)."""
import sys
sys.setrecursionlimit(100000)
sys.path.insert(0, 'src')

from core.lang import Var, In, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq
from core.proof import qed, same
from core.zfc import ZFCAxiom
from theorems.tm import Phase1P, Phase2P, Phase3P, Phase4P, Phase5P

from theorems.tm import TMReachesCompose
is_axiom = lambda f: isinstance(f, (ZFCAxiom, Phase2P, Phase3P, Phase4P, Phase5P, TMReachesCompose))

def test():
    from theorems.tm import tm_add_correct
    from tm import add_goal
    proof = tm_add_correct()
    goal = add_goal()
    assert qed(proof, is_axiom), 'qed failed'
    assert same(proof.sequent.right[0], goal, expand=False), \
        f'conclusion mismatch:\n  got:  {proof.sequent.right[0]}\n  want: {goal}'
    print('tm_add_correct VERIFIED — matches add_goal')

if __name__ == '__main__':
    test()
