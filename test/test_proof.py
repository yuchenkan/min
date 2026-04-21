"""Test the deduction engine with modus ponens."""

import sys
sys.path.insert(0, 'src')

from core import Var, In, Not, Implies, Forall, Sequent, Proof, verify


def test_modus_ponens():
    """Prove: A, A->B |- B"""
    x, y, z = Var(), Var(), Var()
    A = In(x, y)
    B = In(y, z)

    # axiom: A |- A
    ax1 = Proof(Sequent([A], [A]), 'axiom')

    # weakening_right: A |- A, B
    w1 = Proof(Sequent([A], [A, B]), 'weakening_right', [ax1])

    # axiom: A, B |- B
    ax2 = Proof(Sequent([A, B], [B]), 'axiom')

    # implies_left: A, A->B |- B
    mp = Proof(Sequent([A, Implies(A, B)], [B]), 'implies_left', [w1, ax2])

    assert verify(ax1)
    assert verify(w1)
    assert verify(ax2)
    assert verify(mp)


def test_not_not():
    """Prove: A |- ~~A"""
    x, y = Var(), Var()
    A = In(x, y)

    # axiom: A |- A
    ax = Proof(Sequent([A], [A]), 'axiom')

    # not_left: A, ~A |- (empty right)
    nl = Proof(Sequent([A, Not(A)], []), 'not_left', [ax])

    # not_right: A |- ~~A
    nn = Proof(Sequent([A], [Not(Not(A))]), 'not_right', [nl])

    assert verify(ax)
    assert verify(nl)
    assert verify(nn)


def test_forall_instantiation():
    """Prove: Ax(x in y) |- z in y"""
    x, y, z = Var(), Var(), Var()

    body = In(x, y)          # x in y
    instance = In(z, y)      # z in y
    universal = Forall(x, body)

    # axiom: z in y |- z in y
    ax = Proof(Sequent([instance], [instance]), 'axiom')

    # forall_left: Ax(x in y) |- z in y
    fl = Proof(Sequent([universal], [instance]), 'forall_left', [ax])

    assert verify(ax)
    assert verify(fl)


def test_invalid_proof():
    """An invalid proof should fail."""
    x, y, z = Var(), Var(), Var()
    A = In(x, y)
    B = In(y, z)

    # claim A |- B with axiom rule — should fail since A != B
    bad = Proof(Sequent([A], [B]), 'axiom')
    assert not verify(bad)


if __name__ == '__main__':
    test_modus_ponens()
    print('modus ponens: ok')

    test_not_not()
    print('double negation introduction: ok')

    test_forall_instantiation()
    print('forall instantiation: ok')

    test_invalid_proof()
    print('invalid proof rejected: ok')
