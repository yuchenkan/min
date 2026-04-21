"""Test the deduction engine."""

import sys
sys.path.insert(0, 'src')

from core import Var, In, Not, Implies, Forall, Sequent, Proof, verify
from theorems import modus_ponens, double_negation, forall_instantiation


def test_modus_ponens():
    x, y, z = Var(), Var(), Var()
    mp = modus_ponens(In(x, y), In(y, z))
    assert verify(mp)


def test_double_negation():
    x, y = Var(), Var()
    dn = double_negation(In(x, y))
    assert verify(dn)


def test_forall_instantiation():
    x, y, z = Var(), Var(), Var()
    fi = forall_instantiation(x, In(x, y), z)
    assert verify(fi)


def test_invalid_proof():
    x, y, z = Var(), Var(), Var()
    bad = Proof(Sequent([In(x, y)], [In(y, z)]), 'axiom')
    assert not verify(bad)


if __name__ == '__main__':
    test_modus_ponens()
    print('modus ponens: ok')

    test_double_negation()
    print('double negation: ok')

    test_forall_instantiation()
    print('forall instantiation: ok')

    test_invalid_proof()
    print('invalid proof rejected: ok')
