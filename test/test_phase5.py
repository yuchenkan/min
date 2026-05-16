"""Test phase5: prove Phase5P (single step: erase last 1, move R, halt)."""
import sys
sys.setrecursionlimit(100000)
sys.path.insert(0, 'src')

from core.proof import qed, same
from core.zfc import ZFCAxiom
from theorems.tm import Phase5P


def test():
    from theorems.tm import phase5
    proof = phase5()

    goal = Phase5P()
    assert same(proof.sequent.right[0], goal, expand=False), \
        f'conclusion mismatch:\n  got:  {str(proof.sequent.right[0])[:200]}\n  want: {str(goal)[:200]}'

    assert qed(proof, lambda f: isinstance(f, ZFCAxiom)), \
        f'qed failed — non-ZFC on left:\n' + \
        '\n'.join(f'  {str(f)[:80]}' for f in proof.sequent.left if not isinstance(f, ZFCAxiom))

    print('phase5 VERIFIED — proves Phase5P from ZFC')


if __name__ == '__main__':
    test()
