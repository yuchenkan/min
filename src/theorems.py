"""Basic theorems proved from the sequent calculus."""

from core import Var, In, Not, Implies, Forall, Sequent, Proof


def modus_ponens(A, B):
    """A, A->B |- B"""
    return Proof(
        Sequent([A, Implies(A, B)], [B]), 'implies_left',
        [Proof(Sequent([A], [A, B]), 'weakening_right',
            [Proof(Sequent([A], [A]), 'axiom')]),
         Proof(Sequent([A, B], [B]), 'axiom')],
        name='modus_ponens')


def double_negation(A):
    """A |- ~~A"""
    return Proof(
        Sequent([A], [Not(Not(A))]), 'not_right',
        [Proof(Sequent([A, Not(A)], []), 'not_left',
            [Proof(Sequent([A], [A]), 'axiom')])],
        name='double_negation')


def forall_instantiation(x, body, t):
    """forall x. body |- body[t/x]"""
    instance = body.subst(x, t)
    return Proof(
        Sequent([Forall(x, body)], [instance]), 'forall_left',
        [Proof(Sequent([instance], [instance]), 'axiom')],
        name='forall_instantiation')
