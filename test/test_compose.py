"""Test tmreaches_compose: prove TMReachesCompose (chain two TMReaches)."""
import sys
sys.setrecursionlimit(100000)
sys.path.insert(0, 'src')

from core.proof import qed, same
from core.zfc import ZFCAxiom
from theorems.tm import TMReachesCompose


def test():
    from theorems.tm import tmreaches_compose
    proof = tmreaches_compose()

    goal = TMReachesCompose()
    assert same(proof.sequent.right[0], goal, expand=False), \
        f'conclusion mismatch:\n  got:  {str(proof.sequent.right[0])[:200]}\n  want: {str(goal)[:200]}'

    assert qed(proof, lambda f: isinstance(f, ZFCAxiom)), \
        f'qed failed — non-ZFC on left:\n' + \
        '\n'.join(f'  {str(f)[:80]}' for f in proof.sequent.left if not isinstance(f, ZFCAxiom))

    print('tmreaches_compose VERIFIED — proves TMReachesCompose from ZFC')


if __name__ == '__main__':
    test()
