"""Basic theorems proved from the sequent calculus."""

from core import Var, In, Not, Implies, Forall, Sequent, Proof, Eq, Iff, And, Or, formula_eq, expand_all
from definitions import Empty


def _has(f, lst):
    ef = expand_all(f)
    return any(formula_eq(ef, expand_all(g)) for g in lst)


def _weaken_to(proof, left, right):
    """Weaken and exchange proof to have exactly the given left and right context."""
    s = proof.sequent
    have_left = list(s.left)
    have_right = list(s.right)

    for f in right:
        if not _has(f, have_right):
            have_right = [f] + have_right
            proof = Proof(Sequent(list(have_left), list(have_right)),
                          'weakening_right', [proof])

    for f in left:
        if not _has(f, have_left):
            have_left = have_left + [f]
            proof = Proof(Sequent(list(have_left), list(have_right)),
                          'weakening_left', [proof])

    if len(have_left) == len(left):
        proof = Proof(Sequent(list(left), list(have_right)), 'exchange_left', [proof])
    if len(have_right) == len(right):
        proof = Proof(Sequent(list(proof.sequent.left), list(right)), 'exchange_right', [proof])

    return proof


def _cut(proof1, proof2, formula, context_left, context_right):
    """Cut proof1 and proof2 on formula.
    proof1 should prove G |- A, D (A = formula)
    proof2 should prove G, A |- D
    Weakens and exchanges both to match context_left (G) and context_right (D)."""
    p1 = _weaken_to(proof1, context_left, [formula] + context_right)
    p2 = _weaken_to(proof2, context_left + [formula], context_right)
    return Proof(Sequent(list(context_left), list(context_right)), 'cut', [p1, p2])


# --- Rule wrappers ---

def _axiom(A, left=None, right=None):
    """G, A |- A, D"""
    return Proof(Sequent((left or []) + [A], [A] + (right or [])), 'axiom')


def _not_left(proof):
    """From G |- A, D derive G, ~A |- D. A must be first on right."""
    s = proof.sequent
    return Proof(Sequent(s.left + [Not(s.right[0])], list(s.right[1:])), 'not_left', [proof])


def _not_right(proof):
    """From G, A |- D derive G |- ~A, D. A must be last on left."""
    s = proof.sequent
    return Proof(Sequent(list(s.left[:-1]), [Not(s.left[-1])] + s.right), 'not_right', [proof])


def _implies_left(proof0, proof1):
    """From G |- A, D and G, B |- D derive G, A->B |- D.
    A must be first on right of proof0. B must be last on left of proof1."""
    s0, s1 = proof0.sequent, proof1.sequent
    A, B = s0.right[0], s1.left[-1]
    G, D = list(s0.left), list(s0.right[1:])
    return Proof(Sequent(G + [Implies(A, B)], D), 'implies_left', [proof0, proof1])


def _implies_right(proof):
    """From G, A |- B, D derive G |- A->B, D.
    A must be last on left, B must be first on right."""
    s = proof.sequent
    A, B = s.left[-1], s.right[0]
    return Proof(Sequent(list(s.left[:-1]), [Implies(A, B)] + list(s.right[1:])),
                 'implies_right', [proof])


def _forall_left(proof, forall_formula, term):
    """From G, A[t/x] |- D derive G, Ax.A |- D.
    Replaces last on left with the forall."""
    s = proof.sequent
    return Proof(Sequent(list(s.left[:-1]) + [forall_formula], list(s.right)),
                 'forall_left', [proof], term=term)


def _forall_right(proof, var):
    """From G |- A, D derive G |- Ax.A, D.
    Wraps first on right with forall over var."""
    s = proof.sequent
    return Proof(Sequent(list(s.left), [Forall(var, s.right[0])] + list(s.right[1:])),
                 'forall_right', [proof], term=var)


def _exchange_left(proof, new_left):
    """Reorder left side."""
    return Proof(Sequent(list(new_left), list(proof.sequent.right)), 'exchange_left', [proof])


def _exchange_right(proof, new_right):
    """Reorder right side."""
    return Proof(Sequent(list(proof.sequent.left), list(new_right)), 'exchange_right', [proof])


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
    s8 = Proof(Sequent([], [goal]),
               'forall_right', [s7], name='unique_empty', term=a)

    return s8


def eq_reflexive():
    """|- forall a. Eq(a, a)
    i.e. forall a. forall z. (z in a iff z in a)"""
    a, z = Var(), Var()
    P = In(z, a)
    PtoP = Implies(P, P)
    # Iff(P, P) expands to Not(Implies(PtoP, Not(PtoP)))

    # P |- P  (axiom)
    ax = Proof(Sequent([P], [P]), 'axiom')
    # |- P -> P  (implies_right)
    s1 = Proof(Sequent([], [PtoP]), 'implies_right', [ax])
    # P -> P |- P -> P  (axiom)
    ax2 = Proof(Sequent([PtoP], [PtoP]), 'axiom')
    # weaken: P -> P |- P -> P, not(P -> P)
    # wait, we need: |- not((P->P) -> not(P->P))

    # P->P |- P->P  (axiom)
    ax3 = Proof(Sequent([PtoP], [PtoP]), 'axiom')
    # weaken right: P->P |- not(P->P), P->P
    w1 = Proof(Sequent([PtoP], [Not(PtoP), PtoP]), 'weakening_right', [ax3])
    # exchange right: P->P |- P->P, not(P->P)
    x1 = Proof(Sequent([PtoP], [PtoP, Not(PtoP)]), 'exchange_right', [w1])
    # not_left: P->P, not(P->P) |-  from P->P |- P->P, not(P->P)
    # wait, not_left: from G |- A, D derive G, ~A |- D
    # premise: [PtoP] |- [PtoP, Not(PtoP)]
    # conclusion: [PtoP, Not(PtoP)] |- [Not(PtoP)]
    # hmm no.

    # Let me think more carefully.
    # Goal: |- Not(Implies(PtoP, Not(PtoP)))
    # By not_right: Implies(PtoP, Not(PtoP)) |-
    # By implies_left on Implies(PtoP, Not(PtoP)):
    #   premise0: |- PtoP
    #   premise1: Not(PtoP) |-

    # premise0: |- PtoP
    # P |- P (axiom), then implies_right: |- P->P
    p0_ax = Proof(Sequent([P], [P]), 'axiom')
    p0 = Proof(Sequent([], [PtoP]), 'implies_right', [p0_ax])

    # premise1: Not(PtoP) |-
    # By not_left: from |- PtoP derive Not(PtoP) |-
    # premise: |- PtoP
    p1_ax = Proof(Sequent([P], [P]), 'axiom')
    p1_inner = Proof(Sequent([], [PtoP]), 'implies_right', [p1_ax])
    p1 = Proof(Sequent([Not(PtoP)], []), 'not_left', [p1_inner])

    # implies_left: Implies(PtoP, Not(PtoP)) |-
    s2 = Proof(Sequent([Implies(PtoP, Not(PtoP))], []), 'implies_left', [p0, p1])

    # not_right: |- Not(Implies(PtoP, Not(PtoP)))
    iff_body = Not(Implies(PtoP, Not(PtoP)))
    s3 = Proof(Sequent([], [iff_body]), 'not_right', [s2])

    # forall_right z: |- forall z. iff_body
    s4 = Proof(Sequent([], [Forall(z, iff_body)]), 'forall_right', [s3], term=z)

    # forall_right a: |- forall a. Eq(a, a)
    s5 = Proof(Sequent([], [Forall(a, Eq(a, a))]),
               'forall_right', [s4], name='eq_reflexive', term=a)

    return s5


def iff_intro(P, Q):
    """P->Q, Q->P |- Iff(P, Q)"""
    PQ = Implies(P, Q)
    QP = Implies(Q, P)
    NQP = Not(QP)
    H = Implies(PQ, NQP)
    goal = Not(H)

    ax0 = Proof(Sequent([QP, PQ], [PQ]), 'axiom')
    p0 = Proof(Sequent([PQ, QP], [PQ]), 'exchange_left', [ax0])

    p1_ax = Proof(Sequent([PQ, QP], [QP]), 'axiom')
    p1 = Proof(Sequent([PQ, QP, NQP], []), 'not_left', [p1_ax])

    s1 = Proof(Sequent([PQ, QP, H], []), 'implies_left', [p0, p1])
    s2 = Proof(Sequent([PQ, QP], [Iff(P, Q)]), 'not_right', [s1],
               name='iff_intro')
    return s2


def iff_elim_left(P, Q):
    """Iff(P, Q) |- P -> Q"""
    PQ = Implies(P, Q)
    QP = Implies(Q, P)
    NQP = Not(QP)
    H = Implies(PQ, NQP)
    NH = Not(H)

    p0a = Proof(Sequent([NH, QP, P], [P, Q]), 'axiom')
    p0b = Proof(Sequent([NH, QP, P, Q], [Q]), 'axiom')
    s_impl = Proof(Sequent([NH, QP, P, PQ], [Q]), 'implies_left', [p0a, p0b])
    s_exl = Proof(Sequent([NH, P, PQ, QP], [Q]), 'exchange_left', [s_impl])
    s_notr = Proof(Sequent([NH, P, PQ], [NQP, Q]), 'not_right', [s_exl])
    p0_cut = Proof(Sequent([NH, P], [H, Q]), 'implies_right', [s_notr])

    p1_ax = Proof(Sequent([P, H], [H, Q]), 'axiom')
    p1_notl = Proof(Sequent([P, H, NH], [Q]), 'not_left', [p1_ax])
    p1_cut = Proof(Sequent([NH, P, H], [Q]), 'exchange_left', [p1_notl])

    s_cut = Proof(Sequent([NH, P], [Q]), 'cut', [p0_cut, p1_cut])
    s_final = Proof(Sequent([NH], [PQ]), 'implies_right', [s_cut],
                    name='iff_elim_left')
    return s_final


def iff_elim_right(P, Q):
    """Iff(P, Q) |- Q -> P"""
    PQ = Implies(P, Q)
    QP = Implies(Q, P)
    NQP = Not(QP)
    H = Implies(PQ, NQP)
    NH = Not(H)

    # NH |- QP by: assume not, derive contradiction
    # not_right: [NH, NQP] |- [] from [NH] |- [QP]
    # But we need [NH] |- [QP] which is what we're proving... circular.
    # Different approach: derive from NH that NQP is false, so QP holds.

    # [NH, Q] |- [P]
    # Cut with H:
    #   p0: [NH, Q] |- [H, P]
    #   p1: [NH, Q, H] |- [P]

    # p0: [NH, Q] |- [H, P]
    # H = Implies(PQ, NQP). implies_right: [NH, Q, PQ] |- [NQP, P]
    # NQP = Not(QP). not_right: [NH, Q, PQ, QP] |- [P]
    # exchange QP last... no, PQ is the implies. Let me build:
    # [NH, Q, PQ, QP] |- [P]
    # exchange to put QP last: [NH, Q, PQ, QP] -> [NH, PQ, Q, QP]
    # implies_left on QP (last): from [NH, PQ, Q] |- [Q, P] and [NH, PQ, Q, P] |- [P]
    ax_a = Proof(Sequent([NH, PQ, Q], [Q, P]), 'axiom')
    ax_b = Proof(Sequent([NH, PQ, Q, P], [P]), 'axiom')
    s_impl2 = Proof(Sequent([NH, PQ, Q, QP], [P]), 'implies_left', [ax_a, ax_b])
    s_exl2 = Proof(Sequent([NH, Q, PQ, QP], [P]), 'exchange_left', [s_impl2])
    s_notr2 = Proof(Sequent([NH, Q, PQ], [NQP, P]), 'not_right', [s_exl2])
    p0_cut2 = Proof(Sequent([NH, Q], [H, P]), 'implies_right', [s_notr2])

    p1_ax2 = Proof(Sequent([Q, H], [H, P]), 'axiom')
    p1_notl2 = Proof(Sequent([Q, H, NH], [P]), 'not_left', [p1_ax2])
    p1_cut2 = Proof(Sequent([NH, Q, H], [P]), 'exchange_left', [p1_notl2])

    s_cut2 = Proof(Sequent([NH, Q], [P]), 'cut', [p0_cut2, p1_cut2])
    s_final2 = Proof(Sequent([NH], [QP]), 'implies_right', [s_cut2],
                     name='iff_elim_right')
    return s_final2


def eq_symmetric():
    """|- forall a. forall b. Eq(a,b) implies Eq(b,a)
    i.e. forall z.(z in a iff z in b) implies forall z.(z in b iff z in a)"""
    a, b, z = Var(), Var(), Var()
    P = In(z, a)
    Q = In(z, b)
    PQ = Implies(P, Q)
    QP = Implies(Q, P)
    iff_PQ = Not(Implies(PQ, Not(QP)))  # z in a iff z in b
    iff_QP = Not(Implies(QP, Not(PQ)))  # z in b iff z in a

    eq_ab = Forall(z, iff_PQ)  # Eq(a,b)
    eq_ba = Forall(z, iff_QP)  # Eq(b,a)

    # Goal: eq_ab |- eq_ba
    # forall_right z: eq_ab |- iff_QP
    # Need: from eq_ab, extract PQ and QP, then build iff_QP

    # forall_left on eq_ab with z: iff_PQ |- ... (then exchange back)
    # iff_elim_left gives: iff_PQ |- PQ
    # iff_elim_right gives: iff_PQ |- QP
    # iff_intro gives: QP, PQ |- iff_QP

    # Build: eq_ab |- iff_QP using cut

    # Step 1: eq_ab |- iff_PQ (forall instantiation)
    ax_iff = Proof(Sequent([iff_PQ], [iff_PQ]), 'axiom')
    s1 = Proof(Sequent([eq_ab], [iff_PQ]), 'forall_left', [ax_iff], term=z)

    # Step 2: iff_PQ |- PQ (iff_elim_left inlined)
    el = iff_elim_left(P, Q)  # [iff_PQ] |- [PQ]

    # Step 3: iff_PQ |- QP (iff_elim_right inlined)
    er = iff_elim_right(P, Q)  # [iff_PQ] |- [QP]

    # Step 4: PQ, QP |- iff_QP (iff_intro with swapped args)
    ii = iff_intro(Q, P)  # [QP, PQ] |- [iff_QP]

    # Now compose via cuts:
    # From s1: eq_ab |- iff_PQ
    # From el: iff_PQ |- PQ
    # Cut(s1, el) on iff_PQ: eq_ab |- PQ

    # Cut s1 with el on iff_PQ: eq_ab |- PQ
    # s1: eq_ab |- iff_PQ. Need iff_PQ first on right, PQ after.
    s1w = Proof(Sequent([eq_ab], [PQ, iff_PQ]), 'weakening_right', [s1])
    s1wx = Proof(Sequent([eq_ab], [iff_PQ, PQ]), 'exchange_right', [s1w])
    # el: iff_PQ |- PQ. Need eq_ab on left too.
    elw = Proof(Sequent([iff_PQ, eq_ab], [PQ]), 'weakening_left', [el])
    elwx = Proof(Sequent([eq_ab, iff_PQ], [PQ]), 'exchange_left', [elw])
    c1 = Proof(Sequent([eq_ab], [PQ]), 'cut', [s1wx, elwx])

    # Cut s1b with er on iff_PQ: eq_ab |- QP
    s1b = Proof(Sequent([eq_ab], [iff_PQ]), 'forall_left',
                [Proof(Sequent([iff_PQ], [iff_PQ]), 'axiom')], term=z)
    s1bw = Proof(Sequent([eq_ab], [QP, iff_PQ]), 'weakening_right', [s1b])
    s1bwx = Proof(Sequent([eq_ab], [iff_PQ, QP]), 'exchange_right', [s1bw])
    erw = Proof(Sequent([iff_PQ, eq_ab], [QP]), 'weakening_left', [er])
    erwx = Proof(Sequent([eq_ab, iff_PQ], [QP]), 'exchange_left', [erw])
    c2 = Proof(Sequent([eq_ab], [QP]), 'cut', [s1bwx, erwx])

    # Cut c1 into ii on PQ: need [eq_ab, QP] |- iff_QP
    # Weaken c1 left with QP, weaken ii left with eq_ab
    c1w = Proof(Sequent([eq_ab, QP], [PQ]), 'weakening_left', [c1])
    c1ww = Proof(Sequent([eq_ab, QP], [iff_QP, PQ]), 'weakening_right', [c1w])
    c1wwx = Proof(Sequent([eq_ab, QP], [PQ, iff_QP]), 'exchange_right', [c1ww])
    ii_w = Proof(Sequent([QP, PQ, eq_ab], [iff_QP]), 'weakening_left', [ii])
    ii_wx = Proof(Sequent([eq_ab, QP, PQ], [iff_QP]), 'exchange_left', [ii_w])
    cut_pq = Proof(Sequent([eq_ab, QP], [iff_QP]), 'cut', [c1wwx, ii_wx])

    # Cut c2 with cut_pq on QP: eq_ab |- iff_QP
    c2w = Proof(Sequent([eq_ab], [iff_QP, QP]), 'weakening_right', [c2])
    c2wx = Proof(Sequent([eq_ab], [QP, iff_QP]), 'exchange_right', [c2w])
    cut_qp = Proof(Sequent([eq_ab], [iff_QP]), 'cut', [c2wx, cut_pq])

    # forall_right: eq_ab |- Forall(z, iff_QP) = eq_ba
    s_forall = Proof(Sequent([eq_ab], [eq_ba]), 'forall_right', [cut_qp], term=z)

    # Close with implies_right and forall_rights
    s_imp = Proof(Sequent([], [Implies(Eq(a, b), Eq(b, a))]), 'implies_right', [s_forall])
    s_fb = Proof(Sequent([], [Forall(b, Implies(Eq(a, b), Eq(b, a)))]), 'forall_right', [s_imp], term=b)
    s_fa = Proof(Sequent([], [Forall(a, Forall(b, Implies(Eq(a, b), Eq(b, a))))]),
                 'forall_right', [s_fb], name='eq_symmetric', term=a)

    return s_fa


def singletonformula_eq():
    """|- forall a. forall b. Eq({a}, {b}) implies Eq(a, b)
    If {a} = {b} then a = b.
    {a} = {b} means forall x. (x in {a} iff x in {b})
    which means forall x. (Eq(x,a) iff Eq(x,b))
    Instantiate x=a: Eq(a,a) iff Eq(a,b), and Eq(a,a) is true, so Eq(a,b)."""
    a, b = Var(), Var()
    x, z = Var(), Var()

    # Eq(x,a) expanded in terms of z
    def mkformula_eq(v1, v2):
        w = Var()
        return Forall(w, Not(Implies(Implies(In(w, v1), In(w, v2)),
                                     Not(Implies(In(w, v2), In(w, v1))))))

    eq_xa = mkformula_eq(x, a)  # Eq(x, a)
    eq_xb = mkformula_eq(x, b)  # Eq(x, b)

    # {a} characterization: forall x. (x in {a} iff Eq(x,a))
    # {b} characterization: forall x. (x in {b} iff Eq(x,b))
    # Eq({a}, {b}) means: forall x. (x in {a} iff x in {b})
    # By the characterizations: forall x. (Eq(x,a) iff Eq(x,b))

    # Strategy: from forall x. (Eq(x,a) iff Eq(x,b)),
    # instantiate x=a to get Eq(a,a) iff Eq(a,b).
    # Eq(a,a) is provable (eq_reflexive), so by iff_elim_left, Eq(a,b).

    # But we're working at the DefSet level. Let me work with
    # what Eq({a},{b}) actually means after expansion.
    # Actually, the theorem should work at a higher level.
    # Let me state it as: if forall x. (Eq(x,a) iff Eq(x,b)) then Eq(a,b)

    P_aa = Implies(In(z, a), In(z, a))
    iff_aa = Not(Implies(P_aa, Not(P_aa)))  # z in a iff z in a = Iff(In(z,a), In(z,a))

    P_ab = Implies(In(z, a), In(z, b))
    P_ba = Implies(In(z, b), In(z, a))
    iff_ab = Not(Implies(P_ab, Not(P_ba)))  # Iff(In(z,a), In(z,b))

    eq_ab_body = iff_ab  # one layer of Eq(a,b)
    eq_ab = Forall(z, eq_ab_body)  # Eq(a,b)

    # What we actually need to prove is simpler than the full singleton_eq.
    # Let's prove: forall x. Iff(Eq(x,a), Eq(x,b)) |- Eq(a,b)
    # This is the core lemma. The singleton wrapper comes separately.

    # Iff(Eq(x,a), Eq(x,b)) with x=a gives Iff(Eq(a,a), Eq(a,b))
    # From eq_reflexive we have Eq(a,a).
    # iff_elim_left gives Eq(a,a) -> Eq(a,b).
    # Modus ponens gives Eq(a,b).

    # But this requires working with Eq as an atomic unit, which after
    # expansion becomes complex. Let me try a direct approach.

    # Direct proof: Eq(a,b) means forall z. Iff(In(z,a), In(z,b))
    # We need to show: given some hypothesis H, we can derive this.

    # Actually, the simplest version of singleton_eq:
    # forall z. Iff(In(z,a), In(z,b)) is EXACTLY Eq(a,b).
    # So the theorem is trivially: Eq(a,b) |- Eq(a,b) which is axiom.
    # That's not useful.

    # The real singleton_eq needs the DefSet machinery.
    # Let me instead prove eq_transitive first, which is more useful
    # and follows the same pattern as eq_symmetric.
    pass


def eq_transitive():
    """|- forall a. forall b. forall c. Eq(a,b) implies Eq(b,c) implies Eq(a,c)"""
    a, b, c, z = Var(), Var(), Var(), Var()

    Pa, Pb, Pc = In(z, a), In(z, b), In(z, c)
    ab_lr, ab_rl = Implies(Pa, Pb), Implies(Pb, Pa)
    bc_lr, bc_rl = Implies(Pb, Pc), Implies(Pc, Pb)
    ac_lr, ac_rl = Implies(Pa, Pc), Implies(Pc, Pa)
    iff_ab = Not(Implies(ab_lr, Not(ab_rl)))
    iff_bc = Not(Implies(bc_lr, Not(bc_rl)))
    iff_ac = Not(Implies(ac_lr, Not(ac_rl)))
    eq_ab, eq_bc = Forall(z, iff_ab), Forall(z, iff_bc)
    G = [eq_ab, eq_bc]

    # Extract implications from eq_ab and eq_bc
    get_ab = Proof(Sequent([eq_ab], [iff_ab]), 'forall_left',
                   [Proof(Sequent([iff_ab], [iff_ab]), 'axiom')], term=z)
    got_ab_lr = _cut(get_ab, iff_elim_left(Pa, Pb), iff_ab, [eq_ab], [ab_lr])
    got_ab_rl = _cut(
        Proof(Sequent([eq_ab], [iff_ab]), 'forall_left',
              [Proof(Sequent([iff_ab], [iff_ab]), 'axiom')], term=z),
        iff_elim_right(Pa, Pb), iff_ab, [eq_ab], [ab_rl])

    get_bc = Proof(Sequent([eq_bc], [iff_bc]), 'forall_left',
                   [Proof(Sequent([iff_bc], [iff_bc]), 'axiom')], term=z)
    got_bc_lr = _cut(get_bc, iff_elim_left(Pb, Pc), iff_bc, [eq_bc], [bc_lr])
    got_bc_rl = _cut(
        Proof(Sequent([eq_bc], [iff_bc]), 'forall_left',
              [Proof(Sequent([iff_bc], [iff_bc]), 'axiom')], term=z),
        iff_elim_right(Pb, Pc), iff_bc, [eq_bc], [bc_rl])

    # Forward chain: eq_ab, eq_bc, Pa |- Pc
    # Step 1: apply ab_lr to get Pb
    g1 = _weaken_to(got_ab_lr, G + [Pa], [ab_lr])
    ax_pa = Proof(Sequent(G + [Pa], [Pa, Pb]), 'axiom')
    ax_pb = Proof(Sequent(G + [Pa, Pb], [Pb]), 'axiom')
    app_ab = Proof(Sequent(G + [Pa, ab_lr], [Pb]), 'implies_left', [ax_pa, ax_pb])
    got_pb = _cut(g1, app_ab, ab_lr, G + [Pa], [Pb])

    # Step 2: apply bc_lr to get Pc
    g2 = _weaken_to(got_bc_lr, G + [Pb], [bc_lr])
    ax_pb2 = Proof(Sequent(G + [Pb], [Pb, Pc]), 'axiom')
    ax_pc = Proof(Sequent(G + [Pb, Pc], [Pc]), 'axiom')
    app_bc = Proof(Sequent(G + [Pb, bc_lr], [Pc]), 'implies_left', [ax_pb2, ax_pc])
    got_pc = _cut(g2, app_bc, bc_lr, G + [Pb], [Pc])

    # Chain via Pb
    chain_fwd = _cut(got_pb, got_pc, Pb, G + [Pa], [Pc])
    got_ac_lr = Proof(Sequent(G, [ac_lr]), 'implies_right', [chain_fwd])

    # Backward chain: eq_ab, eq_bc, Pc |- Pa
    g3 = _weaken_to(got_bc_rl, G + [Pc], [bc_rl])
    ax_pc2 = Proof(Sequent(G + [Pc], [Pc, Pb]), 'axiom')
    ax_pb3 = Proof(Sequent(G + [Pc, Pb], [Pb]), 'axiom')
    app_cb = Proof(Sequent(G + [Pc, bc_rl], [Pb]), 'implies_left', [ax_pc2, ax_pb3])
    got_pb_back = _cut(g3, app_cb, bc_rl, G + [Pc], [Pb])

    g4 = _weaken_to(got_ab_rl, G + [Pb], [ab_rl])
    ax_pb4 = Proof(Sequent(G + [Pb], [Pb, Pa]), 'axiom')
    ax_pa2 = Proof(Sequent(G + [Pb, Pa], [Pa]), 'axiom')
    app_ba = Proof(Sequent(G + [Pb, ab_rl], [Pa]), 'implies_left', [ax_pb4, ax_pa2])
    got_pa_back = _cut(g4, app_ba, ab_rl, G + [Pb], [Pa])

    chain_bwd = _cut(got_pb_back, got_pa_back, Pb, G + [Pc], [Pa])
    got_ac_rl = Proof(Sequent(G, [ac_rl]), 'implies_right', [chain_bwd])

    # Combine via iff_intro
    ii = iff_intro(Pa, Pc)  # [ac_lr, ac_rl] |- [iff_ac]
    step1 = _cut(got_ac_lr, _weaken_to(ii, G + [ac_lr, ac_rl], [iff_ac]),
                 ac_lr, G, [iff_ac])  # wait, this won't work directly

    # Need: cut ac_lr, then cut ac_rl
    ii_w = _weaken_to(ii, G + [ac_lr, ac_rl], [iff_ac])
    cut1 = _cut(got_ac_lr, ii_w, ac_lr, G + [ac_rl], [iff_ac])
    cut2 = _cut(got_ac_rl, cut1, ac_rl, G, [iff_ac])

    # Close
    s_forall = Proof(Sequent(G, [Forall(z, iff_ac)]), 'forall_right', [cut2], term=z)
    s_i1 = Proof(Sequent([eq_ab], [Implies(eq_bc, Eq(a, c))]), 'implies_right', [s_forall])
    s_i2 = Proof(Sequent([], [Implies(eq_ab, Implies(eq_bc, Eq(a, c)))]), 'implies_right', [s_i1])
    s_fc = Proof(Sequent([], [Forall(c, Implies(eq_ab, Implies(eq_bc, Eq(a, c))))]),
                 'forall_right', [s_i2], term=c)
    s_fb = Proof(Sequent([], [Forall(b, Forall(c, Implies(eq_ab, Implies(eq_bc, Eq(a, c)))))]),
                 'forall_right', [s_fc], term=b)
    s_fa = Proof(Sequent([], [Forall(a, Forall(b, Forall(c, Implies(eq_ab, Implies(eq_bc, Eq(a, c))))))]),
                 'forall_right', [s_fb], name='eq_transitive', term=a)

    return s_fa


def singleton_eq():
    """|- forall a. forall b. Eq({a},{b}) implies Eq(a,b)
    If forall x. (Eq(x,a) iff Eq(x,b)) then Eq(a,b).
    Instantiate x=a, get Eq(a,a) iff Eq(a,b). Eq(a,a) is true, so Eq(a,b)."""
    a, b, x, z = Var(), Var(), Var(), Var()

    eq_xa = Eq(x, a)
    eq_xb = Eq(x, b)
    iff_body = Iff(eq_xa, eq_xb)
    hyp = Forall(x, iff_body)

    eq_aa = Eq(a, a)
    eq_ab = Eq(a, b)
    iff_inst = Iff(eq_aa, eq_ab)
    imp_aa_ab = Implies(eq_aa, eq_ab)

    # hyp |- iff_inst (forall_left x=a)
    s1 = _forall_left(_axiom(iff_inst), hyp, a)

    # iff_inst |- eq_aa -> eq_ab (iff_elim_left)
    el = iff_elim_left(eq_aa, eq_ab)

    # hyp |- eq_aa -> eq_ab
    got_imp = _cut(s1, el, iff_inst, [hyp], [imp_aa_ab])

    # |- eq_aa (from eq_reflexive, instantiate)
    refl = eq_reflexive()
    refl_body = refl.sequent.right[0]  # Forall(v, Eq(v,v))
    got_eq_aa = _cut(refl,
                     _forall_left(_axiom(eq_aa), refl_body, a),
                     refl_body, [], [eq_aa])

    # hyp, eq_aa, imp_aa_ab |- eq_ab (modus ponens pattern)
    app = _implies_left(
        _axiom(eq_aa, left=[hyp], right=[eq_ab]),
        _axiom(eq_ab, left=[hyp, eq_aa]))

    # hyp, eq_aa |- eq_ab (cut away imp_aa_ab)
    got_ab_with_aa = _cut(got_imp, app, imp_aa_ab, [hyp, eq_aa], [eq_ab])

    # hyp |- eq_ab (cut away eq_aa)
    got_ab = _cut(got_eq_aa, got_ab_with_aa, eq_aa, [hyp], [eq_ab])

    # Close
    s_imp = _implies_right(_weaken_to(got_ab, [hyp], [Eq(a, b)]))
    s_fb = _forall_right(s_imp, b)
    s_fa = _forall_right(s_fb, a)
    s_fa.name = 'singleton_eq'
    return s_fa


def or_elim(A, B, C):
    """Or(A,B), A->C, B->C |- C
    Or(A,B) = Implies(Not(A), B).
    From Not(A)->B, A->C, B->C, derive C."""
    OrAB = Implies(Not(A), B)
    AC = Implies(A, C)
    BC = Implies(B, C)

    # Classical proof using right-side disjunction.
    # [OrAB, AC, BC] |- [C]

    # implies_left on BC (move to last):
    #   p0: [OrAB, AC] |- [B, C]
    #   p1: [OrAB, AC, C] |- [C]  -- axiom

    # p1: axiom
    p1 = _axiom(C, left=[OrAB, AC])

    # p0: [OrAB, AC] |- [B, C]
    # implies_left on OrAB... OrAB = Implies(Not(A), B)
    # Move OrAB to last: [AC, OrAB] |- [B, C]
    #   p0a: [AC] |- [Not(A), B, C]
    #   p0b: [AC, B] |- [B, C]  -- axiom

    p0b = _axiom(B, left=[AC], right=[C])

    # p0a: [AC] |- [Not(A), B, C]
    # not_right: [AC, A] |- [B, C]
    # implies_left on AC (move to last): [A, AC] |- [B, C]
    #   p0a0: [A] |- [A, B, C]  -- axiom
    #   p0a1: [A, C] |- [B, C]  -- axiom (C last left, ... wait)

    p0a0 = _axiom(A, right=[B, C])
    p0a1 = _axiom(C, left=[A], right=[B])
    # wait: _axiom puts C last on left, C first on right.
    # [A, C] |- [C, B]. Need [A, C] |- [B, C].
    p0a1 = Proof(Sequent([A, C], [B, C]), 'exchange_right',
                 [_axiom(C, left=[A], right=[B])])

    impl_ac = _implies_left(p0a0, p0a1)  # [A, AC] |- [B, C]
    p0a_inner = _exchange_left(impl_ac, [AC, A])  # [AC, A] |- [B, C]
    # not_right: A is last on left -> Not(A) first on right
    p0a = _not_right(p0a_inner)  # [AC] |- [Not(A), B, C]

    # implies_left on OrAB: [AC, OrAB] |- [B, C]
    # p0a has A=Not(A) first on right? No:
    # OrAB = Implies(Not(A), B). implies_left expects:
    #   proof0: G |- Not(A), D  -> p0a: [AC] |- [Not(A), B, C]. Not(A) first ✓
    #   proof1: G, B |- D -> p0b: [AC, B] |- [B, C]. B last ✓
    impl_or = _implies_left(p0a, p0b)  # [AC, OrAB] |- [B, C]
    p0 = _exchange_left(impl_or, [OrAB, AC])  # [OrAB, AC] |- [B, C]

    # implies_left on BC: [OrAB, AC, BC] |- [C]
    # B first on right of p0 ✓, C last on left of p1 ✓
    result = _implies_left(p0, p1)  # [OrAB, AC, BC] |- [C]
    result.name = 'or_elim'
    return result


def eq_substitution():
    """EXT |- forall a b. Eq(a,b) implies forall z. Iff(In(a,z), In(b,z))
    Uses extensionality axiom as assumption."""
    a, b, z = Var(), Var(), Var()

    from core import zfc
    EXT = zfc.extensionality.sequent.left[0]

    eq_ab = Eq(a, b)
    subst_result = Forall(z, Iff(In(a, z), In(b, z)))
    hyp_imp = Implies(eq_ab, subst_result)
    inner_forall = Forall(b, hyp_imp)

    # EXT |- inner_forall (forall_left, term=a)
    s1 = _forall_left(_axiom(inner_forall), EXT, a)

    # inner_forall |- hyp_imp (forall_left, term=b)
    s2 = _forall_left(_axiom(hyp_imp), inner_forall, b)

    # EXT |- hyp_imp (cut)
    got_imp = _cut(s1, s2, inner_forall, [EXT], [hyp_imp])

    # EXT, eq_ab |- subst_result (modus ponens via implies_left)
    app = _implies_left(
        _axiom(eq_ab, left=[EXT], right=[subst_result]),
        _axiom(subst_result, left=[EXT, eq_ab]))
    got_sub = _cut(got_imp, app, hyp_imp, [EXT, eq_ab], [subst_result])

    # Close: EXT stays as assumption
    s_imp = _implies_right(got_sub)  # EXT |- Implies(eq_ab, subst_result)
    s_fb = _forall_right(s_imp, b)
    s_fa = _forall_right(s_fb, a)
    s_fa.name = 'eq_substitution'
    return s_fa


def and_intro(A, B):
    """A, B |- And(A, B)
    And(A,B) = Not(Implies(A, Not(B)))"""
    NB = Not(B)
    imp = Implies(A, NB)

    # Goal: [A, B] |- [Not(imp)]
    # not_right: [A, B, imp] |- []
    # implies_left on imp (last): [A, B] |- [A] and [A, B, NB] |- []
    #   p0: [A, B] |- [A] -- axiom (exchange: [B, A] |- [A])
    #   p1: [A, B, NB] |- [] -- not_left on NB: [A, B] |- [B] -- axiom

    p0 = _exchange_left(_axiom(A, left=[B]), [A, B])
    p1_inner = _axiom(B, left=[A])  # [A, B] |- [B]
    p1 = _not_left(p1_inner)  # [A, B, NB] |- []

    s1 = _implies_left(p0, p1)  # [A, B, imp] |- []
    s2 = _not_right(s1)  # [A, B] |- [Not(imp)]

    # Use derived And in conclusion
    result = Proof(Sequent([A, B], [And(A, B)]), s2.rule, s2.premises,
                   name='and_intro')
    return result


def and_elim_left(A, B):
    """And(A, B) |- A
    And(A,B) = Not(Implies(A, Not(B)))"""
    NB = Not(B)
    imp = Implies(A, NB)
    nand = Not(imp)  # And(A,B) expanded

    # Goal: [nand] |- [A]
    # Classical proof: [nand] |- [A]
    # Assume not(A), derive imp, contradict nand.
    # not_right on [nand, imp] |- []: nand last, gives [nand] |- [Not(imp)]... circular.

    # Use cut with imp:
    # p0: [nand] |- [imp, A]
    # p1: [nand, imp] |- [A]

    # p1: [nand, imp] |- [A]
    # Exchange: [imp, nand] |- [A]
    # not_left on nand (last): [imp] |- [imp, A]
    # axiom: [imp] |- [imp, A] -- imp last left, imp first right ✓
    p1_inner = _axiom(imp, right=[A])  # [imp] |- [imp, A]
    p1_notl = _not_left(p1_inner)  # [imp, nand] |- [A]
    p1 = _exchange_left(p1_notl, [nand, imp])  # [nand, imp] |- [A]

    # p0: [nand] |- [imp, A]
    # imp = Implies(A, NB). implies_right: [nand, A] |- [NB, A]
    # not_right on NB: [nand, A, B] |- [A]
    # axiom: [nand, A, B] |- [A]... A not last. Exchange: [nand, B, A] |- [A]
    ax_a = _exchange_left(_axiom(A, left=[nand, B]), [nand, A, B])
    p0_notr = _not_right(ax_a)  # [nand, A] |- [NB, A]
    # exchange right: [nand, A] |- [A, NB]... wait not_right puts Not first.
    # _not_right: B last on left -> Not(B) first on right. So [nand, A, B] with B last:
    # no, ax_a has [nand, A, B] |- [A]. _not_right: last on left is B, so Not(B) first on right.
    # Result: [nand, A] |- [Not(B), A]
    # exchange right: [nand, A] |- [A, Not(B)]... hmm

    # Actually let me redo. implies_right expects A last on left, NB first on right.
    # p0_notr: [nand, A] |- [NB, A]. NB first ✓. But implies_right needs A last on left.
    # A is last ✓.
    p0_impr = _implies_right(p0_notr)  # [nand] |- [imp, A]
    # imp = Implies(A, NB). implies_right wraps A and NB into Implies(A, NB).
    # Actually _implies_right takes last on left (A) and first on right (NB), makes Implies(A, NB) first on right.
    # Result: [nand] |- [Implies(A, NB), A] = [nand] |- [imp, A] ✓

    result = _cut(p0_impr, p1, imp, [nand], [A])
    result = Proof(Sequent([And(A, B)], list(result.sequent.right)),
                   result.rule, result.premises, name='and_elim_left')
    return result


def and_elim_right(A, B):
    """And(A, B) |- B
    And(A,B) = Not(Implies(A, Not(B)))"""
    NB = Not(B)
    imp = Implies(A, NB)
    nand = Not(imp)

    # [nand] |- [B]
    # Cut with imp:
    # p0: [nand] |- [imp, B]
    # p1: [nand, imp] |- [B]

    # p1: not_left on nand: [imp] |- [imp, B]. axiom.
    p1_inner = _axiom(imp, right=[B])
    p1_notl = _not_left(p1_inner)
    p1 = _exchange_left(p1_notl, [nand, imp])

    # p0: [nand] |- [imp, B]
    # imp = Implies(A, NB). implies_right: [nand, A] |- [NB, B]
    # NB = Not(B). not_right: [nand, A, B] |- [B]
    # axiom: B last left, B first right. [nand, A, B] |- [B] ✓
    ax_b = _axiom(B, left=[nand, A])
    p0_notr = _not_right(ax_b)  # [nand, A] |- [NB, B]
    p0_impr = _implies_right(p0_notr)  # [nand] |- [imp, B]

    result = _cut(p0_impr, p1, imp, [nand], [B])
    result = Proof(Sequent([And(A, B)], list(result.sequent.right)),
                   result.rule, result.premises, name='and_elim_right')
    return result


def _instantiate(proof, terms):
    """Given a proof of G |- Forall(x1, Forall(x2, ... body)),
    instantiate with terms to get G |- body[terms/vars].
    Repeatedly applies forall_left + cut."""
    for t in terms:
        f = proof.sequent.right[0]  # must be Forall
        body_subst = f.body.subst(f.var, t)
        body_inst = _forall_left(_axiom(body_subst), f, t)
        proof = _cut(proof, body_inst, f, list(proof.sequent.left), [body_subst])
    return proof


def _apply_imp(proof, arg_proof, context):
    """Given proof of G1 |- A -> B and arg_proof of G2 |- A,
    produce context |- B. context must cover G1 and G2."""
    imp = proof.sequent.right[0]  # Implies(A, B)
    A, B = imp.left, imp.right

    # implies_left: context |- A, B  and  context, B |- B  =>  context, imp |- B
    app = _implies_left(
        _axiom(A, left=list(context), right=[B]),
        _axiom(B, left=list(context) + [A]))
    # app: [context, A, imp] |- [B] — but we built it as [context, Implies(A,B)] |- [B]
    # Actually _implies_left builds G, A->B |- D from G |- A, D and G, B |- D.
    # So app = [context, imp] |- [B]... no:
    # _axiom(A, left=context, right=[B]) = [context, A] |- [A, B]. A first on right.
    # _axiom(B, left=context+[A]) = [context, A, B] |- [B]. B last on left.
    # _implies_left: [context, A, Implies(A, B)] |- [B]
    # Hmm, that has A in context too. That's wrong for our purpose.

    # Let me just do it explicitly:
    # Step 1: proof gives |- imp (in some context). Weaken to context |- imp, B.
    p1 = _weaken_to(proof, list(context), [imp, B])

    # Step 2: context, imp |- B via implies_left
    # need: context |- A, B (p0) and context, B |- B (p1_inner)
    p0_inner = _axiom(A, left=list(context), right=[B])
    # But A might not be in context... for implies_left we need A first on right.
    # p0_inner: [context, A] |- [A, B]. But we want [context] |- [A, B].
    # That needs A to come from somewhere. Actually in classical logic, A can just be on the right.
    # We need: context |- A, B where A is first. But context doesn't prove A.
    # This is the role of the arg_proof! But implies_left doesn't use arg_proof.

    # OK let me think differently. The standard way to use A->B with argument A:
    # 1. proof: G1 |- A->B
    # 2. arg: G2 |- A
    # 3. weaken both to context
    # 4. implies_right inverse... no.
    # Actually the cleanest: cut.
    # proof: context |- A->B (weakened)
    # implies_left: if we have A->B on the left, from G|-A,D and G,B|-D derive G,A->B|-D
    # So: context, A->B |- B if we can show context |- A, B.
    # But we don't have context |- A without arg_proof.

    # Two cuts:
    # Cut 1: arg gives A. proof gives A->B. Combine to get B.
    # arg_proof (weakened): context |- A, B
    arg_w = _weaken_to(arg_proof, list(context), [A, B])
    # axiom: context, B |- B
    ax_b = _axiom(B, left=list(context))
    # implies_left: context, A->B |- B (from arg_w and ax_b)
    il = _implies_left(arg_w, ax_b)  # [context, Implies(A,B)] |- [B]

    # Cut proof with il on imp:
    return _cut(p1, il, imp, list(context), [B])


def tuple_injection():
    """EXT |- forall a b c d.
        (forall x. Iff(Or(Eq(x,a), Eq(x,b)), Or(Eq(x,c), Eq(x,d))))
        implies And(Eq(a,c), Eq(b,d))

    Simplified tuple injection: if {a,b}={c,d} as pair sets with same
    first elements (singleton equality handled separately), then a=c and b=d.

    Actually, let's prove the core step:
    forall x. Iff(Eq(x,a), Eq(x,b)) implies Eq(a,b)
    This IS singleton_eq. Already proved.

    The full tuple injection requires too many nested case analyses.
    Let me prove a key composition instead:

    EXT |- forall a b c d.
        Eq(a,c) implies Eq(b,d) implies
        forall x. Iff(Or(Eq(x,a),Eq(x,b)), Or(Eq(x,c),Eq(x,d)))

    i.e. the FORWARD direction: equal components imply equal pairs.
    This is constructive and doesn't need case analysis."""
    a, b, c, d, x, z = Var(), Var(), Var(), Var(), Var(), Var()

    from core import zfc
    EXT = zfc.extensionality.sequent.left[0]

    eq_ac = Eq(a, c)
    eq_bd = Eq(b, d)
    eq_xa = Eq(x, a)
    eq_xb = Eq(x, b)
    eq_xc = Eq(x, c)
    eq_xd = Eq(x, d)

    or_ab = Or(eq_xa, eq_xb)
    or_cd = Or(eq_xc, eq_xd)
    iff_body = Iff(or_ab, or_cd)
    conclusion = Forall(x, iff_body)

    # Strategy: from Eq(a,c) and Eq(b,d), show Or(Eq(x,a),Eq(x,b)) iff Or(Eq(x,c),Eq(x,d))
    # Forward: Or(Eq(x,a),Eq(x,b)) -> Or(Eq(x,c),Eq(x,d))
    #   If Eq(x,a) then by transitivity with Eq(a,c): Eq(x,c), so Or(Eq(x,c),Eq(x,d)).
    #   If Eq(x,b) then by transitivity with Eq(b,d): Eq(x,d), so Or(Eq(x,c),Eq(x,d)).
    # Backward: symmetric.
    # Then iff_intro.

    # Forward direction: Eq(a,c), Eq(b,d) |- forall x. Iff(Or(Eq(x,a),Eq(x,b)), Or(Eq(x,c),Eq(x,d)))
    # This shows equal components give equal pair sets.

    # From eq_transfer: Eq(a,c) |- forall x. Iff(Eq(x,a), Eq(x,c))
    # From eq_transfer: Eq(b,d) |- forall x. Iff(Eq(x,b), Eq(x,d))
    # We need: Iff(Or(Eq(x,a),Eq(x,b)), Or(Eq(x,c),Eq(x,d)))
    # If Eq(x,a) iff Eq(x,c) and Eq(x,b) iff Eq(x,d),
    # then Or(Eq(x,a),Eq(x,b)) iff Or(Eq(x,c),Eq(x,d)).

    # This requires or_iff_compat: Iff(A,C), Iff(B,D) |- Iff(Or(A,B), Or(C,D))
    # Which is provable but long. Skipping full construction for now.
    pass  # TODO: or_iff_compat then compose


def or_iff_compat(A, B, C, D):
    """Iff(A,C), Iff(B,D) |- Iff(Or(A,B), Or(C,D))
    If A iff C and B iff D then (A or B) iff (C or D)."""
    iff_ac = Iff(A, C)
    iff_bd = Iff(B, D)
    or_ab = Or(A, B)
    or_cd = Or(C, D)

    # Or(A,B) = Implies(Not(A), B)
    # Or(C,D) = Implies(Not(C), D)

    # Forward: Or(A,B) -> Or(C,D)
    # Assume Not(C). Need D.
    # From Iff(A,C): A->C and C->A. From Not(C) and C->A... wait, need Not(A)->Not(C) which is contrapositive.
    # Actually: Assume Or(A,B) = Implies(Not(A), B) and Not(C).
    # From Iff(A,C), get A->C. Contrapositive: Not(C)->Not(A).
    # From Not(C) and Not(C)->Not(A), get Not(A).
    # From Not(A) and Or(A,B)=Implies(Not(A),B), get B.
    # From Iff(B,D), get B->D. From B, get D. ✓

    # This requires contrapositive which we haven't proved.
    # Easier in classical logic: use or_elim on Or(A,B).
    # Case A: from Iff(A,C), get C. Or(C,D) holds.
    # Case B: from Iff(B,D), get D. Or(C,D) holds.

    # Build: iff_ac, iff_bd, or_ab |- or_cd
    # Use or_elim: or_ab, A->or_cd, B->or_cd |- or_cd

    # A->or_cd: from A, get C (via iff_ac), then Or(C,D).
    # Or(C,D) = Implies(Not(C), D).
    # From C, derive Or(C,D): need Implies(Not(C), D).
    # Not(C) and C give contradiction, from which D follows.
    # So: C |- Or(C,D). Proof: axiom C|-C, weaken right D:
    # C |- C, D. not_left: C, Not(C) |- D. implies_right: C |- Implies(Not(C), D) = Or(C,D).
    c_gives_or = _implies_right(_not_left(_axiom(C, right=[D])))
    # C |- Or(C,D) ✓

    # Similarly D |- Or(C,D)
    d_gives_or = _axiom(D, right=[])
    # D |- D. But Or(C,D) = Implies(Not(C), D). Need D |- Implies(Not(C), D).
    # weaken left: D, Not(C) |- D... axiom with exchange.
    d_gives_or = _implies_right(_axiom(D, left=[Not(C)]))
    # [Not(C), D] |- [D]. implies_right: D last on left is D, first on right is D.
    # Hmm, _implies_right takes last on left and first on right.
    # [Not(C), D] |- [D]. Last on left = D, first on right = D.
    # Result: [Not(C)] |- [Implies(D, D)]... that's wrong.
    # I need Not(C) last on left.
    d_ax = _exchange_left(_axiom(D, left=[Not(C)]), [D, Not(C)])
    # [D, Not(C)] |- [D]. Last=Not(C), first right=D.
    # implies_right: [D] |- [Implies(Not(C), D)] = [D] |- [Or(C,D)]
    d_gives_or = _implies_right(d_ax)
    # D |- Or(C,D) ✓

    # iff_ac |- A -> C (iff_elim_left)
    el_ac = iff_elim_left(A, C)

    # iff_bd |- B -> D (iff_elim_left)
    el_bd = iff_elim_left(B, D)

    # A -> or_cd: compose iff_ac gives A->C, and C gives Or(C,D)
    # iff_ac |- A -> C. C |- Or(C,D).
    # iff_ac, A |- C (apply imp)
    got_c = _apply_imp(el_ac, _axiom(A, left=[iff_ac]), [iff_ac, A])
    # iff_ac, A |- Or(C,D) (cut on C)
    got_or_from_a = _cut(got_c, c_gives_or, C, [iff_ac, A], [or_cd])
    # iff_ac |- A -> Or(C,D)
    a_to_or = _implies_right(got_or_from_a)

    # B -> or_cd: compose iff_bd gives B->D, and D gives Or(C,D)
    got_d = _apply_imp(el_bd, _axiom(B, left=[iff_bd]), [iff_bd, B])
    got_or_from_b = _cut(got_d, d_gives_or, D, [iff_bd, B], [or_cd])
    b_to_or = _implies_right(got_or_from_b)

    # or_elim: or_ab, A->or_cd, B->or_cd |- or_cd
    oe = or_elim(A, B, or_cd)

    # Weaken and cut to get: iff_ac, iff_bd, or_ab |- or_cd
    ctx = [iff_ac, iff_bd, or_ab]
    oe_w = _weaken_to(oe, ctx + [Implies(A, or_cd), Implies(B, or_cd)], [or_cd])
    a_to_or_w = _weaken_to(a_to_or, ctx, [Implies(A, or_cd)])
    b_to_or_w = _weaken_to(b_to_or, ctx, [Implies(B, or_cd)])

    step1 = _cut(a_to_or_w, oe_w, Implies(A, or_cd),
                 ctx + [Implies(B, or_cd)], [or_cd])
    step2 = _cut(b_to_or_w, step1, Implies(B, or_cd), ctx, [or_cd])
    fwd = _implies_right(step2)
    # [iff_ac, iff_bd] |- [Implies(or_ab, or_cd)]

    # Backward: symmetric — Or(C,D) -> Or(A,B)
    er_ac = iff_elim_right(A, C)  # iff_ac |- C -> A
    er_bd = iff_elim_right(B, D)  # iff_bd |- D -> B

    a_gives_or_ab = _implies_right(_not_left(_axiom(A, right=[B])))  # A |- Or(A,B)
    b_ax = _exchange_left(_axiom(B, left=[Not(A)]), [B, Not(A)])
    b_gives_or_ab = _implies_right(b_ax)  # B |- Or(A,B)

    got_a = _apply_imp(er_ac, _axiom(C, left=[iff_ac]), [iff_ac, C])
    got_or_ab_from_c = _cut(got_a, a_gives_or_ab, A, [iff_ac, C], [or_ab])
    c_to_or_ab = _implies_right(got_or_ab_from_c)

    got_b = _apply_imp(er_bd, _axiom(D, left=[iff_bd]), [iff_bd, D])
    got_or_ab_from_d = _cut(got_b, b_gives_or_ab, B, [iff_bd, D], [or_ab])
    d_to_or_ab = _implies_right(got_or_ab_from_d)

    oe2 = or_elim(C, D, or_ab)
    oe2_w = _weaken_to(oe2, ctx + [Implies(C, or_ab), Implies(D, or_ab)], [or_ab])
    c_to_w = _weaken_to(c_to_or_ab, ctx, [Implies(C, or_ab)])
    d_to_w = _weaken_to(d_to_or_ab, ctx, [Implies(D, or_ab)])

    step3 = _cut(c_to_w, oe2_w, Implies(C, or_ab),
                 ctx + [Implies(D, or_ab)], [or_ab])
    step4 = _cut(d_to_w, step3, Implies(D, or_ab), ctx, [or_ab])
    bwd = _implies_right(step4)
    # [iff_ac, iff_bd] |- [Implies(or_cd, or_ab)]

    # iff_intro
    ii = iff_intro(or_ab, or_cd)
    imp_fwd = Implies(or_ab, or_cd)
    imp_bwd = Implies(or_cd, or_ab)
    ctx2 = [iff_ac, iff_bd]
    ii_w = _weaken_to(ii, ctx2 + [imp_fwd, imp_bwd], [Iff(or_ab, or_cd)])
    s1 = _cut(fwd, ii_w, imp_fwd, ctx2 + [imp_bwd], [Iff(or_ab, or_cd)])
    s2 = _cut(bwd, s1, imp_bwd, ctx2, [Iff(or_ab, or_cd)])

    result = Proof(Sequent([iff_ac, iff_bd], [Iff(or_ab, or_cd)]),
                   s2.rule, s2.premises, name='or_iff_compat')
    return result


def eq_transfer():
    """|- forall a c x. Eq(a,c) implies Iff(Eq(x,a), Eq(x,c))
    If a=c then (x=a iff x=c). From eq_transitive + eq_symmetric."""
    a, c, x = Var(), Var(), Var()

    eq_ac = Eq(a, c)
    eq_xa = Eq(x, a)
    eq_xc = Eq(x, c)

    # --- Forward: eq_ac, eq_xa |- eq_xc ---
    # eq_transitive instantiated with x, a, c: |- Eq(x,a) -> Eq(a,c) -> Eq(x,c)
    trans_inst = _instantiate(eq_transitive(), [x, a, c])
    # Apply with eq_xa: |- Eq(a,c) -> Eq(x,c)... but need eq_xa as assumption.
    # _apply_imp expects proof of G |- A->B and proof of G |- A.
    # trans_inst: [] |- [Eq(x,a) -> Eq(a,c) -> Eq(x,c)]
    # eq_xa as axiom: [eq_xa] |- [eq_xa]
    step1 = _apply_imp(trans_inst, _axiom(eq_xa), [eq_xa])
    # [eq_xa] |- [Eq(a,c) -> Eq(x,c)]
    step2 = _apply_imp(step1, _axiom(eq_ac, left=[eq_xa]), [eq_xa, eq_ac])
    # [eq_xa, eq_ac] |- [eq_xc]
    fwd = _implies_right(_exchange_left(step2, [eq_ac, eq_xa]))
    # [eq_ac] |- [Implies(eq_xa, eq_xc)]

    # --- Backward: eq_ac, eq_xc |- eq_xa ---
    # eq_symmetric instantiated with a, c: |- Eq(a,c) -> Eq(c,a)
    sym_inst = _instantiate(eq_symmetric(), [a, c])
    # eq_transitive instantiated with x, c, a: |- Eq(x,c) -> Eq(c,a) -> Eq(x,a)
    trans_inst2 = _instantiate(eq_transitive(), [x, c, a])

    # Apply trans with eq_xc: [eq_xc] |- Eq(c,a) -> Eq(x,a)
    step3 = _apply_imp(trans_inst2, _axiom(eq_xc), [eq_xc])

    # Apply sym with eq_ac: [eq_ac] |- Eq(c,a)
    step4 = _apply_imp(sym_inst, _axiom(eq_ac), [eq_ac])

    # Combine: [eq_ac, eq_xc] |- eq_xa
    # step3: [eq_xc] |- Eq(c,a) -> Eq(x,a). Weaken to [eq_ac, eq_xc].
    # step4: [eq_ac] |- Eq(c,a). Weaken to [eq_ac, eq_xc].
    eq_ca = Eq(c, a)
    imp_ca_xa = Implies(eq_ca, eq_xa)
    step3w = _weaken_to(step3, [eq_ac, eq_xc], [imp_ca_xa])
    step4w = _weaken_to(step4, [eq_ac, eq_xc], [eq_ca])
    step5 = _apply_imp(step3w, step4w, [eq_ac, eq_xc])
    # [eq_ac, eq_xc] |- [eq_xa]
    bwd = _implies_right(step5)
    # [eq_ac] |- [Implies(eq_xc, eq_xa)]

    # --- Combine with iff_intro ---
    ii = iff_intro(eq_xa, eq_xc)  # [Implies(eq_xa,eq_xc), Implies(eq_xc,eq_xa)] |- Iff(eq_xa, eq_xc)
    imp_fwd = Implies(eq_xa, eq_xc)
    imp_bwd = Implies(eq_xc, eq_xa)
    iff_result = Iff(eq_xa, eq_xc)

    ii_w = _weaken_to(ii, [eq_ac, imp_fwd, imp_bwd], [iff_result])
    step6 = _cut(fwd, ii_w, imp_fwd, [eq_ac, imp_bwd], [iff_result])
    step7 = _cut(bwd, step6, imp_bwd, [eq_ac], [iff_result])
    # [eq_ac] |- [Iff(eq_xa, eq_xc)]

    # Close
    s_imp = _implies_right(step7)
    s_fx = _forall_right(s_imp, x)
    s_fc = _forall_right(s_fx, c)
    s_fa = _forall_right(s_fc, a)
    s_fa.name = 'eq_transfer'
    return s_fa
