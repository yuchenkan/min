"""Basic theorems proved from the sequent calculus."""

from core import Var, In, Not, Implies, Forall, Sequent, Proof, Eq
from definitions import Empty


def modus_ponens(A, B):
    """A, A->B |- B"""
    # implies_left: principal A->B last on left
    # premise0: G |- f.left, D  i.e. [A] |- [A, B]
    # premise1: G, f.right |- D  i.e. [A, B] |- [B]
    ax1 = Proof(Sequent([A], [A]), 'axiom')
    w1 = Proof(Sequent([A], [B, A]), 'weakening_right', [ax1])
    p0 = Proof(Sequent([A], [A, B]), 'exchange_right', [w1])
    ax2 = Proof(Sequent([A, B], [B]), 'axiom')
    return Proof(
        Sequent([A, Implies(A, B)], [B]), 'implies_left',
        [p0, ax2],
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
        name='forall_instantiation', term=t)


def unique_empty():
    """Empty(a => Empty(b => a = b)): two empty sets are equal."""
    goal = Empty(lambda a: Empty(lambda b: Eq(a, b)))

    a, b, z = Var(), Var(), Var()
    x1, x2 = Var(), Var()
    H1 = Forall(x1, Not(In(x1, a)))
    H2 = Forall(x2, Not(In(x2, b)))

    P = In(z, a)
    Q = In(z, b)
    PtoQ = Implies(P, Q)
    QtoP = Implies(Q, P)
    eq_body = Not(Implies(PtoQ, Not(QtoP)))

    # Core: H1, H2 |- forall z. eq_body
    leaf0 = Proof(Sequent([H2, P], [P, Q]), 'axiom')
    s0a = Proof(Sequent([H2, P, Not(P)], [Q]), 'not_left', [leaf0])
    # exchange H1 to last: [H2, P, Not(P)] -> [H2, P, H1] after forall_left
    s0b = Proof(Sequent([H2, P, H1], [Q]), 'forall_left', [s0a], term=z)
    s0b2 = Proof(Sequent([H1, H2, P], [Q]), 'exchange_left', [s0b])
    s0c = Proof(Sequent([H1, H2], [PtoQ]), 'implies_right', [s0b2])

    leaf1 = Proof(Sequent([H1, Q], [Q, P]), 'axiom')
    s1a = Proof(Sequent([H1, Q, Not(Q)], [P]), 'not_left', [leaf1])
    # exchange H2 to last: [H1, Q, Not(Q)] -> [H1, Q, H2] after forall_left
    s1b = Proof(Sequent([H1, Q, H2], [P]), 'forall_left', [s1a], term=z)
    s1b2 = Proof(Sequent([H1, H2, Q], [P]), 'exchange_left', [s1b])
    s1c = Proof(Sequent([H1, H2], [QtoP]), 'implies_right', [s1b2])
    s1d = Proof(Sequent([H1, H2, Not(QtoP)], []), 'not_left', [s1c])

    s2 = Proof(Sequent([H1, H2, Implies(PtoQ, Not(QtoP))], []),
               'implies_left', [s0c, s1d])
    s3 = Proof(Sequent([H1, H2], [eq_body]), 'not_right', [s2])
    s4 = Proof(Sequent([H1, H2], [Forall(z, eq_body)]), 'forall_right', [s3], term=z)

    # Close: |- goal
    s5 = Proof(Sequent([H1], [Implies(H2, Forall(z, eq_body))]), 'implies_right', [s4])
    s6 = Proof(Sequent([H1], [Forall(b, Implies(H2, Forall(z, eq_body)))]), 'forall_right', [s5], term=b)
    s7 = Proof(Sequent([], [Implies(H1, Forall(b, Implies(H2, Forall(z, eq_body))))]), 'implies_right', [s6])
    s8 = Proof(Sequent([], [Forall(a, Implies(H1, Forall(b, Implies(H2, Forall(z, eq_body)))))]),
               'forall_right', [s7], name='unique_empty', term=a)

    return s8
