"""Test phase1: prove Phase1P (scan right past a ones in a steps)."""
import sys
sys.setrecursionlimit(100000)
sys.path.insert(0, 'src')

from core.proof import qed, same
from core.zfc import ZFCAxiom
from theorems.tm import Phase1P

def test():
    from theorems.tm import phase1
    proof = phase1()

    goal = Phase1P()
    assert same(proof.sequent.right[0], goal, expand=False), \
        f'conclusion mismatch:\n  got:  {str(proof.sequent.right[0])[:200]}\n  want: {str(goal)[:200]}'

    # All left formulas must be ZFC axioms
    assert qed(proof, lambda f: isinstance(f, ZFCAxiom)), \
        f'qed failed — non-ZFC on left:\n' + \
        '\n'.join(f'  {str(f)[:80]}' for f in proof.sequent.left if not isinstance(f, ZFCAxiom))

    print('phase1 VERIFIED — proves Phase1P from ZFC')


if __name__ == '__main__':
    test()
