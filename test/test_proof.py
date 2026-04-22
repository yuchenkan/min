"""Test the deduction engine."""

import sys
sys.path.insert(0, 'src')

from core import Var, In, Not, Implies, Forall, Sequent, Proof, verify


def test_modus_ponens():
    x, y, z = Var(), Var(), Var()
    A, B = In(x, y), In(y, z)
    imp = Implies(A, B)

    ax1 = Proof(Sequent([A], [A]), 'axiom', principal=A)
    w = Proof(Sequent([A], [A, B]), 'weakening_right', [ax1], principal=B)
    ax2 = Proof(Sequent([A, B], [B]), 'axiom', principal=B)
    mp = Proof(Sequent([A, imp], [B]), 'implies_left', [w, ax2], principal=imp)
    assert verify(mp)


def test_double_negation():
    x, y = Var(), Var()
    A = In(x, y)
    na = Not(A)
    nna = Not(na)

    ax = Proof(Sequent([A], [A]), 'axiom', principal=A)
    nl = Proof(Sequent([A, na], []), 'not_left', [ax], principal=na)
    nn = Proof(Sequent([A], [nna]), 'not_right', [nl], principal=nna)
    assert verify(nn)


def test_forall_instantiation():
    x, y, z = Var(), Var(), Var()
    body = In(x, y)
    instance = In(z, y)
    universal = Forall(x, body)

    ax = Proof(Sequent([instance], [instance]), 'axiom', principal=instance)
    fl = Proof(Sequent([universal], [instance]), 'forall_left', [ax],
               principal=universal, term=z)
    assert verify(fl)


def test_invalid_proof():
    x, y, z = Var(), Var(), Var()
    A, B = In(x, y), In(y, z)
    bad = Proof(Sequent([A], [B]), 'axiom', principal=A)
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
