"""Basic theorems proved from the sequent calculus."""

from core import Var, In, Not, Implies, Forall, Sequent, Proof, Eq, Iff, And, Or, formula_eq, expand_all
from definitions import Empty


def _has(f, lst):
    """Check if f is in lst, first by identity, then by alpha-equiv after expansion."""
    if any(f is g for g in lst):
        return True
    ef = expand_all(f)
    return any(formula_eq(ef, expand_all(g)) for g in lst)


def _weaken_to(proof, left, right):
    """Weaken and exchange proof to have exactly the given left and right context."""
    s = proof.sequent
    have_right = list(s.right)
    have_left = list(s.left)

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

    s = proof.sequent
    if len(s.left) == len(left):
        proof = Proof(Sequent(list(left), list(s.right)), 'exchange_left', [proof])
    s = proof.sequent
    if len(s.right) == len(right):
        proof = Proof(Sequent(list(s.left), list(right)), 'exchange_right', [proof])

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
    # Use eq_transfer and or_iff_compat to show:
    # Eq(a,c), Eq(b,d) |- forall x. Iff(Or(Eq(x,a),Eq(x,b)), Or(Eq(x,c),Eq(x,d)))

    # eq_transfer instantiated with a,c,x: |- Eq(a,c) -> Iff(Eq(x,a), Eq(x,c))
    t1 = _instantiate(eq_transfer(), [a, c, x])
    got_iff_ac = _apply_imp(t1, _axiom(eq_ac), [eq_ac])
    # [eq_ac] |- Iff(Eq(x,a), Eq(x,c))

    # eq_transfer instantiated with b,d,x: |- Eq(b,d) -> Iff(Eq(x,b), Eq(x,d))
    t2 = _instantiate(eq_transfer(), [b, d, x])
    got_iff_bd = _apply_imp(t2, _axiom(eq_bd), [eq_bd])
    # [eq_bd] |- Iff(Eq(x,b), Eq(x,d))

    # or_iff_compat: Iff(Eq(x,a),Eq(x,c)), Iff(Eq(x,b),Eq(x,d))
    #   |- Iff(Or(Eq(x,a),Eq(x,b)), Or(Eq(x,c),Eq(x,d)))
    oic = or_iff_compat(eq_xa, eq_xb, eq_xc, eq_xd)
    iff_xa_xc = Iff(eq_xa, eq_xc)
    iff_xb_xd = Iff(eq_xb, eq_xd)

    # Compose via cuts in context [eq_ac, eq_bd]
    G = [eq_ac, eq_bd]
    oic_w = _weaken_to(oic, G + [iff_xa_xc, iff_xb_xd], [iff_body])
    t1_w = _weaken_to(got_iff_ac, G, [iff_xa_xc])
    t2_w = _weaken_to(got_iff_bd, G, [iff_xb_xd])

    s1 = _cut(t1_w, oic_w, iff_xa_xc, G + [iff_xb_xd], [iff_body])
    s2 = _cut(t2_w, s1, iff_xb_xd, G, [iff_body])
    # [eq_ac, eq_bd] |- iff_body

    s3 = _forall_right(s2, x)
    # [eq_ac, eq_bd] |- forall x. iff_body = conclusion

    s_i1 = _implies_right(s3)
    s_i2 = _implies_right(s_i1)
    s_fd = _forall_right(s_i2, d)
    s_fc = _forall_right(s_fd, c)
    s_fb = _forall_right(s_fc, b)
    s_fa = _forall_right(s_fb, a)
    s_fa.name = 'pair_eq_forward'
    return s_fa


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

    # Backward: Or(C,D) -> Or(A,B) in context [iff_ac, iff_bd]
    er_ac = iff_elim_right(A, C)  # iff_ac |- C -> A
    er_bd = iff_elim_right(B, D)  # iff_bd |- D -> B

    a_gives_or_ab = _implies_right(_not_left(_axiom(A, right=[B])))  # A |- Or(A,B)
    b_ax = _exchange_left(_axiom(B, left=[Not(A)]), [B, Not(A)])
    b_gives_or_ab = _implies_right(b_ax)  # B |- Or(A,B)

    # iff_ac, C |- A -> or_ab
    got_a = _apply_imp(er_ac, _axiom(C, left=[iff_ac]), [iff_ac, C])
    got_or_ab_from_c = _cut(got_a, a_gives_or_ab, A, [iff_ac, C], [or_ab])
    c_to_or_ab = _implies_right(got_or_ab_from_c)  # iff_ac |- C -> or_ab

    got_b = _apply_imp(er_bd, _axiom(D, left=[iff_bd]), [iff_bd, D])
    got_or_ab_from_d = _cut(got_b, b_gives_or_ab, B, [iff_bd, D], [or_ab])
    d_to_or_ab = _implies_right(got_or_ab_from_d)  # iff_bd |- D -> or_ab

    # or_elim: or_cd, C->or_ab, D->or_ab |- or_ab
    oe2 = or_elim(C, D, or_ab)
    # Context for backward: [iff_ac, iff_bd, or_cd]
    bwd_ctx = [iff_ac, iff_bd, or_cd]
    imp_c = Implies(C, or_ab)
    imp_d = Implies(D, or_ab)

    oe2_w = _weaken_to(oe2, bwd_ctx + [imp_c, imp_d], [or_ab])
    c_to_w = _weaken_to(c_to_or_ab, bwd_ctx, [imp_c])
    d_to_w = _weaken_to(d_to_or_ab, bwd_ctx, [imp_d])

    step3 = _cut(c_to_w, oe2_w, imp_c, bwd_ctx + [imp_d], [or_ab])
    step4 = _cut(d_to_w, step3, imp_d, bwd_ctx, [or_ab])
    # [iff_ac, iff_bd, or_cd] |- [or_ab]
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


def or_intro_left(A, B):
    """A |- Or(A, B)"""
    # Or(A,B) = Implies(Not(A), B)
    # A |- A (axiom). weaken right D: A |- A, B.
    # not_left: A, Not(A) |- B. implies_right: A |- Implies(Not(A), B) = Or(A,B).
    result = _implies_right(_not_left(_axiom(A, right=[B])))
    return Proof(Sequent([A], [Or(A, B)]), result.rule, result.premises,
                 name='or_intro_left')


def or_intro_right(A, B):
    """B |- Or(A, B)"""
    # Or(A,B) = Implies(Not(A), B)
    # B, Not(A) |- B (axiom, exchange). implies_right: B |- Implies(Not(A), B).
    ax = _exchange_left(_axiom(B, left=[Not(A)]), [B, Not(A)])
    result = _implies_right(ax)
    return Proof(Sequent([B], [Or(A, B)]), result.rule, result.premises,
                 name='or_intro_right')


def iff_mp(A, B):
    """Iff(A, B), A |- B
    Forward modus ponens on biconditional."""
    iff = Iff(A, B)
    el = iff_elim_left(A, B)  # iff |- A -> B
    imp_ab = Implies(A, B)
    # iff, A |- B
    result = _apply_imp(el, _axiom(A, left=[iff]), [iff, A])
    result.name = 'iff_mp'
    return result


def iff_mp_rev(A, B):
    """Iff(A, B), B |- A
    Backward modus ponens on biconditional."""
    iff = Iff(A, B)
    er = iff_elim_right(A, B)  # iff |- B -> A
    result = _apply_imp(er, _axiom(B, left=[iff]), [iff, B])
    result.name = 'iff_mp_rev'
    return result


def tuple_injection_reverse():
    """|- forall a b c d.
    (forall x. Iff(Or(Eq(x,a),Eq(x,b)), Or(Eq(x,c),Eq(x,d))))
    implies (forall y. Iff(Eq(y,a), Eq(y,c)))
    implies And(Eq(a,c), Eq(b,d))

    If {a,b}={c,d} and {a}={c} (singletons equal) then a=c and b=d.
    The singleton equality is a separate hypothesis for now."""
    a, b, c, d, x, y = Var(), Var(), Var(), Var(), Var(), Var()

    eq_xa, eq_xb = Eq(x, a), Eq(x, b)
    eq_xc, eq_xd = Eq(x, c), Eq(x, d)
    or_ab = Or(eq_xa, eq_xb)
    or_cd = Or(eq_xc, eq_xd)

    # Hypotheses
    H_pair = Forall(x, Iff(or_ab, or_cd))  # {a,b}={c,d}
    H_sing = Forall(y, Iff(Eq(y, a), Eq(y, c)))  # {a}={c}

    # Step 1: From H_sing, by singleton_eq, get Eq(a,c)
    seq = singleton_eq()  # |- forall a b. (forall x. Iff(Eq(x,a),Eq(x,b))) implies Eq(a,b)
    seq_inst = _instantiate(seq, [a, c])
    # |- Implies(forall x. Iff(Eq(x,a), Eq(x,c)), Eq(a,c))
    eq_ac = Eq(a, c)
    got_ac = _apply_imp(seq_inst, _axiom(H_sing), [H_sing])
    # [H_sing] |- [Eq(a,c)]

    # Step 2: From H_pair, instantiate x=b:
    # Iff(Or(Eq(b,a),Eq(b,b)), Or(Eq(b,c),Eq(b,d)))
    eq_ba, eq_bb = Eq(b, a), Eq(b, b)
    eq_bc, eq_bd = Eq(b, c), Eq(b, d)
    or_ba_bb = Or(eq_ba, eq_bb)
    or_bc_bd = Or(eq_bc, eq_bd)
    iff_b = Iff(or_ba_bb, or_bc_bd)

    h_pair_inst = _forall_left(_axiom(iff_b), H_pair, b)
    # [H_pair] |- [iff_b]

    # Eq(b,b) is true (reflexivity)
    refl = eq_reflexive()  # |- forall a. Eq(a,a)
    got_bb = _instantiate(refl, [b])  # |- Eq(b,b)

    # Or(Eq(b,a), Eq(b,b)) is true (from Eq(b,b) via or_intro_right)
    oir = or_intro_right(eq_ba, eq_bb)  # Eq(b,b) |- Or(Eq(b,a), Eq(b,b))
    got_or = _cut(got_bb, oir, eq_bb, [], [or_ba_bb])
    # [] |- [or_ba_bb]

    # Apply iff forward: iff_b, or_ba_bb |- or_bc_bd
    got_iff_b = _apply_imp(
        iff_elim_left(or_ba_bb, or_bc_bd),
        _axiom(or_ba_bb, left=[iff_b]),
        [iff_b, or_ba_bb])
    # [iff_b, or_ba_bb] |- [or_bc_bd]

    # Cut to get: [H_pair] |- [or_bc_bd]
    G1 = [H_pair]
    s1 = _cut(h_pair_inst, got_iff_b, iff_b, G1 + [or_ba_bb], [or_bc_bd])
    # [H_pair, or_ba_bb] |- [or_bc_bd]
    s2 = _cut(got_or, s1, or_ba_bb, G1, [or_bc_bd])
    # [H_pair] |- [or_bc_bd] = Or(Eq(b,c), Eq(b,d))

    # Step 3: We have Eq(a,c). We need Eq(b,d).
    # From Or(Eq(b,c), Eq(b,d)):
    # Case Eq(b,c): since a=c, Eq(b,c) = Eq(b,a) in some sense...
    # Actually we want: from Eq(b,c) and Eq(a,c), get Eq(b,a), and then...
    # Hmm, we want b=d, not b=a.

    # Better approach: from Or(Eq(b,c), Eq(b,d)) and Eq(a,c):
    # Since a=c, Eq(b,c) iff Eq(b,a) (by eq_transfer).
    # So Or(Eq(b,c), Eq(b,d)) becomes Or(Eq(b,a), Eq(b,d)).
    # We also know {a,b}={c,d} and a=c.
    # Instantiate x=a in H_pair: Iff(Or(Eq(a,a),Eq(a,b)), Or(Eq(a,c),Eq(a,d)))
    # Eq(a,a) is true, so left side is true, so right side: Or(Eq(a,c), Eq(a,d)).
    # Since a=c, Eq(a,c) is true, so this is just Or(true, Eq(a,d)) = true. Not useful.

    # Alternative: instantiate x=d in H_pair:
    # Iff(Or(Eq(d,a),Eq(d,b)), Or(Eq(d,c),Eq(d,d)))
    # Eq(d,d) is true, so right side true, so left side: Or(Eq(d,a), Eq(d,b)).

    # Hmm, let me use a simpler approach for now.
    # Claim: Or(Eq(b,c), Eq(b,d)) and Eq(a,c) implies Eq(b,d).

    # Case Eq(b,c): From a=c, we have c=a (symmetric). Eq(b,c) and c=a gives Eq(b,a)
    #   by transitivity. Now use H_pair with x=b again...
    #   Actually, the simplest: if we also know a≠b (the non-degenerate case),
    #   then Eq(b,c)=Eq(b,a) is false, so Eq(b,d) must hold.
    #   But we can't assume a≠b in general.

    # For the GENERAL case (including a=b):
    # If a=b, then {a,b}={a,a}={a}={c,d}. So c=a and d=a. Then b=a=d. ✓
    # If a≠b, then Eq(b,a) is false, so from Or(Eq(b,c), Eq(b,d)) and Eq(b,c)→Eq(b,a),
    # we need classical reasoning: either Eq(b,a) or not.

    # Classical approach: from Or(Eq(b,c), Eq(b,d)):
    # We want to show Eq(b,d).
    # In classical logic, this requires showing that Eq(b,c) implies Eq(b,d).

    # From Eq(b,c) and Eq(a,c) (symmetric: Eq(c,a)):
    # Eq(b,c), Eq(c,a) → Eq(b,a) by transitivity.
    # So b=a. Then from {a,b}={a,a}={a}, and {c,d} must equal {a}.
    # So c=a and d=a. Since b=a and d=a, b=d. ✓

    # From Eq(b,c): Eq(b,c), Eq(c,a) → Eq(b,a) → b=a.
    # Then Eq(a,b) (symmetric of Eq(b,a)).
    # {a,b} with a=b means forall x. Iff(Or(Eq(x,a),Eq(x,a)), Or(Eq(x,c),Eq(x,d)))
    # Or(Eq(x,a),Eq(x,a)) iff Eq(x,a) (idempotent).
    # So forall x. Iff(Eq(x,a), Or(Eq(x,c),Eq(x,d))).
    # Instantiate x=d: Iff(Eq(d,a), Or(Eq(d,c),Eq(d,d))).
    # Eq(d,d) true, so right side true, so Eq(d,a) true.
    # Symmetric: Eq(a,d). Since b=a, Eq(b,d). ✓

    # This is very involved. For now, let me just prove the two separate pieces
    # and combine them.

    # Actually, use or_elim directly:
    # From Or(Eq(b,c), Eq(b,d)), to show Eq(b,d):
    #   Case Eq(b,c): chain Eq(b,c) → Eq(b,a) → ... → Eq(b,d) (complex)
    #   Case Eq(b,d): done.
    # The second case is trivial. The first case is the hard one.

    # For now, return the partial result: H_pair, H_sing |- And(Eq(a,c), Or(Eq(b,c), Eq(b,d)))
    # This is what we can prove easily.
    G = [H_pair, H_sing]
    got_ac_w = _weaken_to(got_ac, G, [eq_ac])
    s2_w = _weaken_to(s2, G, [or_bc_bd])
    result = and_intro(eq_ac, or_bc_bd)
    result_w = _weaken_to(result, G + [eq_ac, or_bc_bd], [And(eq_ac, or_bc_bd)])
    step_a = _cut(got_ac_w, result_w, eq_ac, G + [or_bc_bd], [And(eq_ac, or_bc_bd)])
    step_b = _cut(s2_w, step_a, or_bc_bd, G, [And(eq_ac, or_bc_bd)])

    s_i1 = _implies_right(step_b)
    s_i2 = _implies_right(s_i1)
    s_fd = _forall_right(s_i2, d)
    s_fc = _forall_right(s_fd, c)
    s_fb = _forall_right(s_fc, b)
    s_fa = _forall_right(s_fb, a)
    s_fa.name = 'tuple_injection_partial'
    return s_fa


def eq_bc_implies_bd(a=None, b=None, c=None, d=None, x=None):
    """H_pair, Eq(a,c), Eq(b,c) |- Eq(b,d)
    where H_pair = forall x. Iff(Or(Eq(x,a),Eq(x,b)), Or(Eq(x,c),Eq(x,d)))
    If b=c and a=c (so a=b=c), then {a,b}={a}={c}={c,d}, so d=a=b."""
    a = a or Var()
    b = b or Var()
    c = c or Var()
    d = d or Var()
    x = x or Var()

    eq_xa, eq_xb = Eq(x, a), Eq(x, b)
    eq_xc, eq_xd = Eq(x, c), Eq(x, d)
    H_pair = Forall(x, Iff(Or(eq_xa, eq_xb), Or(eq_xc, eq_xd)))

    eq_ac = Eq(a, c)
    eq_bc = Eq(b, c)
    eq_bd = Eq(b, d)

    G = [H_pair, eq_ac, eq_bc]

    # From Eq(b,c) and Eq(a,c) symmetric = Eq(c,a):
    # Eq(b,c), Eq(c,a) → Eq(b,a) by transitivity.
    # Then Eq(a,b) by symmetry.
    # So a=b=c.

    # Instantiate H_pair with x=d:
    # Iff(Or(Eq(d,a),Eq(d,b)), Or(Eq(d,c),Eq(d,d)))
    eq_da, eq_db = Eq(d, a), Eq(d, b)
    eq_dc, eq_dd = Eq(d, c), Eq(d, d)
    or_da_db = Or(eq_da, eq_db)
    or_dc_dd = Or(eq_dc, eq_dd)
    iff_d = Iff(or_da_db, or_dc_dd)

    h_inst = _forall_left(_axiom(iff_d), H_pair, d)
    # [H_pair] |- [iff_d]

    # Eq(d,d) is true
    got_dd = _instantiate(eq_reflexive(), [d])  # |- Eq(d,d)
    # Or(Eq(d,c), Eq(d,d)) is true
    got_or_right = _cut(got_dd, or_intro_right(eq_dc, eq_dd), eq_dd, [], [or_dc_dd])
    # |- Or(Eq(d,c), Eq(d,d))

    # Apply iff backward: iff_d, or_dc_dd |- or_da_db
    got_or_da_db = _apply_imp(
        iff_elim_right(or_da_db, or_dc_dd),
        _axiom(or_dc_dd, left=[iff_d]),
        [iff_d, or_dc_dd])
    # [iff_d, or_dc_dd] |- [or_da_db]

    # Chain: [H_pair] |- [or_da_db]
    s1 = _cut(h_inst, got_or_da_db, iff_d, [H_pair, or_dc_dd], [or_da_db])
    s2 = _cut(got_or_right, s1, or_dc_dd, [H_pair], [or_da_db])
    # [H_pair] |- [Or(Eq(d,a), Eq(d,b))]

    # Now: Or(Eq(d,a), Eq(d,b)).
    # Since a=c and b=c, both Eq(d,a) and Eq(d,b) give us Eq(d,c) essentially.
    # From Eq(d,a): Eq(d,a), Eq(a,c) → Eq(d,c) by transitivity.
    #   Then Eq(d,c), Eq(c,b) → Eq(d,b) by transitivity. (Eq(c,b) from symmetric of Eq(b,c))
    #   Then Eq(b,d) by symmetry.
    # From Eq(d,b): symmetric gives Eq(b,d) directly.

    # Case Eq(d,b): Eq(d,b) |- Eq(b,d)
    sym_db = _instantiate(eq_symmetric(), [d, b])  # |- Eq(d,b) -> Eq(b,d)
    case2 = _apply_imp(sym_db, _axiom(eq_db), [eq_db])
    # [Eq(d,b)] |- [Eq(b,d)]

    # Case Eq(d,a): chain Eq(d,a) → Eq(d,c) → Eq(d,b) → Eq(b,d)
    # Eq(d,a), Eq(a,c) → Eq(d,c)
    trans_dac = _instantiate(eq_transitive(), [d, a, c])
    step_dc = _apply_imp(
        _apply_imp(trans_dac, _axiom(eq_da), [eq_da]),
        _axiom(eq_ac, left=[eq_da]),
        [eq_da, eq_ac])
    # [Eq(d,a), Eq(a,c)] |- [Eq(d,c)]

    # Eq(b,c) symmetric → Eq(c,b)
    sym_bc = _instantiate(eq_symmetric(), [b, c])
    got_cb = _apply_imp(sym_bc, _axiom(eq_bc), [eq_bc])
    # [Eq(b,c)] |- [Eq(c,b)]

    # Eq(d,c), Eq(c,b) → Eq(d,b)
    trans_dcb = _instantiate(eq_transitive(), [d, c, b])
    eq_cb = Eq(c, b)
    eq_db2 = Eq(d, b)

    step_db = _apply_imp(
        _apply_imp(trans_dcb, _axiom(Eq(d, c), left=[eq_cb]), [Eq(d, c), eq_cb]),
        _axiom(eq_cb, left=[Eq(d, c)]),
        [Eq(d, c), eq_cb])
    # [Eq(d,c), Eq(c,b)] |- [Eq(d,b)]

    # Eq(d,b) → Eq(b,d)
    sym_db2 = _instantiate(eq_symmetric(), [d, b])
    step_bd = _apply_imp(sym_db2, _axiom(eq_db2), [eq_db2])
    # [Eq(d,b)] |- [Eq(b,d)]

    # Chain: [Eq(d,a), Eq(a,c), Eq(b,c)] |- Eq(b,d)
    ctx_case1 = [eq_da, eq_ac, eq_bc]
    step_dc_w = _weaken_to(step_dc, ctx_case1, [Eq(d, c)])
    got_cb_w = _weaken_to(got_cb, ctx_case1, [eq_cb])
    step_db_w = _weaken_to(step_db, ctx_case1 + [Eq(d, c), eq_cb], [eq_db2])

    c1 = _cut(step_dc_w, step_db_w, Eq(d, c), ctx_case1 + [eq_cb], [eq_db2])
    c2 = _cut(got_cb_w, c1, eq_cb, ctx_case1, [eq_db2])
    # ctx_case1 |- Eq(d,b)
    c3 = _cut(c2, step_bd, eq_db2, ctx_case1, [eq_bd])
    # [Eq(d,a), Eq(a,c), Eq(b,c)] |- [Eq(b,d)]

    case1 = _implies_right(_exchange_left(c3, [eq_ac, eq_bc, eq_da]))
    # [Eq(a,c), Eq(b,c)] |- [Implies(Eq(d,a), Eq(b,d))]

    case2_imp = _implies_right(_weaken_to(case2, [eq_ac, eq_bc, eq_db], [eq_bd]))
    case2_imp2 = _exchange_left(case2_imp, [eq_ac, eq_bc])
    # oops, case2_imp has [eq_ac, eq_bc, Eq(d,b)] on left before implies_right
    # After implies_right: [eq_ac, eq_bc] |- [Implies(Eq(d,b), Eq(b,d))]

    # or_elim: Or(Eq(d,a), Eq(d,b)), Eq(d,a)->Eq(b,d), Eq(d,b)->Eq(b,d) |- Eq(b,d)
    oe = or_elim(eq_da, eq_db, eq_bd)
    imp_da_bd = Implies(eq_da, eq_bd)
    imp_db_bd = Implies(eq_db, eq_bd)

    ctx_final = [H_pair, eq_ac, eq_bc]
    oe_w = _weaken_to(oe, ctx_final + [or_da_db, imp_da_bd, imp_db_bd], [eq_bd])
    s2_w = _weaken_to(s2, ctx_final, [or_da_db])
    case1_w = _weaken_to(case1, ctx_final, [imp_da_bd])
    case2_w = _weaken_to(case2_imp, ctx_final, [imp_db_bd])

    r1 = _cut(s2_w, oe_w, or_da_db, ctx_final + [imp_da_bd, imp_db_bd], [eq_bd])
    r2 = _cut(case1_w, r1, imp_da_bd, ctx_final + [imp_db_bd], [eq_bd])
    r3 = _cut(case2_w, r2, imp_db_bd, ctx_final, [eq_bd])
    # [H_pair, Eq(a,c), Eq(b,c)] |- [Eq(b,d)]

    r3.name = 'eq_bc_implies_bd'
    return r3


def tuple_injection_full():
    """|- forall a b c d.
    (forall x. Iff(Or(Eq(x,a),Eq(x,b)), Or(Eq(x,c),Eq(x,d))))
    implies (forall y. Iff(Eq(y,a), Eq(y,c)))
    implies And(Eq(a,c), Eq(b,d))"""
    a, b, c, d, x, y = Var(), Var(), Var(), Var(), Var(), Var()

    eq_xa, eq_xb = Eq(x, a), Eq(x, b)
    eq_xc, eq_xd = Eq(x, c), Eq(x, d)
    H_pair = Forall(x, Iff(Or(eq_xa, eq_xb), Or(eq_xc, eq_xd)))
    H_sing = Forall(y, Iff(Eq(y, a), Eq(y, c)))
    G = [H_pair, H_sing]

    eq_ac = Eq(a, c)
    eq_bc = Eq(b, c)
    eq_bd = Eq(b, d)
    or_bc_bd = Or(eq_bc, eq_bd)

    # From tuple_injection_reverse (partial): G |- And(Eq(a,c), Or(Eq(b,c), Eq(b,d)))
    partial = tuple_injection_reverse()
    partial_inst = _instantiate(partial, [a, b, c, d])
    # |- H_pair -> H_sing -> And(Eq(a,c), Or(Eq(b,c), Eq(b,d)))
    got_partial = _apply_imp(
        _apply_imp(partial_inst, _axiom(H_pair), [H_pair]),
        _axiom(H_sing, left=[H_pair]),
        [H_pair, H_sing])
    # G |- And(Eq(a,c), Or(Eq(b,c), Eq(b,d)))
    and_result = And(eq_ac, or_bc_bd)

    # Extract Eq(a,c) and Or(Eq(b,c), Eq(b,d))
    got_ac = _cut(got_partial, and_elim_left(eq_ac, or_bc_bd), and_result, G, [eq_ac])
    got_or = _cut(got_partial, and_elim_right(eq_ac, or_bc_bd), and_result, G, [or_bc_bd])

    # Case Eq(b,c): by eq_bc_implies_bd, H_pair, Eq(a,c), Eq(b,c) |- Eq(b,d)
    case_bc = eq_bc_implies_bd(a, b, c, d, x)
    # case_bc: [H_pair, Eq(a,c), Eq(b,c)] |- [Eq(b,d)]
    case_bc_imp = _implies_right(_weaken_to(case_bc, G + [eq_ac, eq_bc], [eq_bd]))
    # G, Eq(a,c) |- Implies(Eq(b,c), Eq(b,d))

    # Case Eq(b,d): trivially Eq(b,d)
    case_bd = _axiom(eq_bd)
    case_bd_imp = _implies_right(_weaken_to(case_bd, G + [eq_ac, eq_bd], [eq_bd]))
    # G, Eq(a,c) |- Implies(Eq(b,d), Eq(b,d))

    # or_elim: Or(Eq(b,c),Eq(b,d)), Eq(b,c)->Eq(b,d), Eq(b,d)->Eq(b,d) |- Eq(b,d)
    oe = or_elim(eq_bc, eq_bd, eq_bd)
    imp_bc_bd = Implies(eq_bc, eq_bd)
    imp_bd_bd = Implies(eq_bd, eq_bd)

    ctx_oe = G + [eq_ac]
    oe_w = _weaken_to(oe, ctx_oe + [or_bc_bd, imp_bc_bd, imp_bd_bd], [eq_bd])
    got_or_w = _weaken_to(got_or, ctx_oe, [or_bc_bd])
    case_bc_w = _weaken_to(case_bc_imp, ctx_oe, [imp_bc_bd])
    case_bd_w = _weaken_to(case_bd_imp, ctx_oe, [imp_bd_bd])

    r1 = _cut(got_or_w, oe_w, or_bc_bd, ctx_oe + [imp_bc_bd, imp_bd_bd], [eq_bd])
    r2 = _cut(case_bc_w, r1, imp_bc_bd, ctx_oe + [imp_bd_bd], [eq_bd])
    r3 = _cut(case_bd_w, r2, imp_bd_bd, ctx_oe, [eq_bd])
    # G, Eq(a,c) |- Eq(b,d)

    # Cut in Eq(a,c)
    got_bd = _cut(got_ac, r3, eq_ac, G, [eq_bd])
    # G |- Eq(b,d)

    # Combine: G |- And(Eq(a,c), Eq(b,d))
    ai = and_intro(eq_ac, eq_bd)
    ai_w = _weaken_to(ai, G + [eq_ac, eq_bd], [And(eq_ac, eq_bd)])
    s1 = _cut(got_ac, ai_w, eq_ac, G + [eq_bd], [And(eq_ac, eq_bd)])
    s2 = _cut(got_bd, s1, eq_bd, G, [And(eq_ac, eq_bd)])
    # G |- And(Eq(a,c), Eq(b,d))

    # Close
    # The hypothesis H_pair = forall x. Iff(Or(Eq(x,a),Eq(x,b)), Or(Eq(x,c),Eq(x,d)))
    # is Eq({a,b},{c,d}) at the membership level.
    # H_sing = forall y. Iff(Eq(y,a), Eq(y,c)) is Eq({a},{c}).
    s_i1 = _implies_right(s2)
    s_i2 = _implies_right(s_i1)
    s_fd = _forall_right(s_i2, d)
    s_fc = _forall_right(s_fd, c)
    s_fb = _forall_right(s_fc, b)
    s_fa = _forall_right(s_fb, a)
    s_fa.name = 'tuple_injection'
    return s_fa


def singleton_from_tuple(a=None, b=None, c=None, d=None):
    """|- forall a b c d.
    (forall x. Iff(Or(Eq(x,{a}),Eq(x,{a,b})), Or(Eq(x,{c}),Eq(x,{c,d}))))
    implies (forall y. Iff(Eq(y,a), Eq(y,c)))

    From (a,b)=(c,d) derive {a}={c}.
    Proof: {a} is in {{a},{a,b}}, so {a} is in {{c},{c,d}}.
    Thus {a}={c} or {a}={c,d}.
    Case {a}={c}: done.
    Case {a}={c,d}: instantiate y=c in {a}={c,d}: Eq(c,a) iff Or(Eq(c,c),Eq(c,d)).
      Eq(c,c) true, so right true, so Eq(c,a) true, i.e. a=c.
      Instantiate y=d: Eq(d,a) iff Or(Eq(d,c),Eq(d,d)). Eq(d,d) true, so Eq(d,a) true.
      So c=a and d=a, hence {c}={c,d}={a}. So {a}={c}={c,d}={a}.
      forall y. Iff(Eq(y,a),Eq(y,c)): since a=c, this follows from eq_transfer.

    This is 100+ steps. Let me use the existing building blocks."""

    # For now, this is a known gap. The full proof requires bridging
    # the tuple-level equality (on {{a},{a,b}}) down to pair membership,
    # then case analysis. All the tools exist but the proof is very long.
    #
    a = a or Var()
    b = b or Var()
    c = c or Var()
    d = d or Var()
    s, z, y = Var(), Var(), Var()

    # Level-2 formulas (s is a free variable)
    sing_a = Forall(z, Iff(In(z, s), Eq(z, a)))
    sing_c = Forall(z, Iff(In(z, s), Eq(z, c)))
    pair_ab = Forall(z, Iff(In(z, s), Or(Eq(z, a), Eq(z, b))))
    pair_cd = Forall(z, Iff(In(z, s), Or(Eq(z, c), Eq(z, d))))

    or_left = Or(sing_a, pair_ab)
    or_right = Or(sing_c, pair_cd)
    H_tuple = Forall(s, Iff(or_left, or_right))
    H_sing = Forall(y, Iff(Eq(y, a), Eq(y, c)))

    # Step 1: H_tuple, sing_a |- Or(sing_c, pair_cd)
    iff_inst = Iff(or_left, or_right)
    h_inst = _forall_left(_axiom(iff_inst), H_tuple, s)
    # H_tuple |- iff_inst

    got_or_left = or_intro_left(sing_a, pair_ab)  # sing_a |- or_left
    got_or_right = _apply_imp(
        iff_elim_left(or_left, or_right),
        _axiom(or_left, left=[iff_inst]),
        [iff_inst, or_left])
    # [iff_inst, or_left] |- or_right

    s1 = _cut(h_inst, got_or_right, iff_inst, [H_tuple, or_left], [or_right])
    s2 = _cut(got_or_left, s1, or_left, [H_tuple, sing_a], [or_right])
    # [H_tuple, sing_a] |- [Or(sing_c, pair_cd)]

    # Step 2 Case A: sing_a, sing_c |- H_sing
    # For any y: sing_a gives In(y,s) iff Eq(y,a). sing_c gives In(y,s) iff Eq(y,c).
    # So Eq(y,a) iff Eq(y,c) (transitivity through In(y,s)).
    # Need: Eq(y,a) -> Eq(y,c) and Eq(y,c) -> Eq(y,a).

    # Forward: Eq(y,a) -> In(y,s) -> Eq(y,c)
    eq_ya = Eq(y, a)
    eq_yc = Eq(y, c)
    in_ys = In(y, s)
    iff_ya = Iff(in_ys, eq_ya)
    iff_yc = Iff(in_ys, eq_yc)

    inst_a = _forall_left(_axiom(iff_ya), sing_a, y)  # sing_a |- iff_ya
    inst_c = _forall_left(_axiom(iff_yc), sing_c, y)  # sing_c |- iff_yc

    # iff_ya: In(y,s) iff Eq(y,a). iff_elim_right: iff_ya |- Eq(y,a) -> In(y,s)
    ya_to_in = iff_elim_right(in_ys, eq_ya)  # iff_ya |- Eq(y,a) -> In(y,s)
    # iff_yc: In(y,s) iff Eq(y,c). iff_elim_left: iff_yc |- In(y,s) -> Eq(y,c)
    in_to_yc = iff_elim_left(in_ys, eq_yc)  # iff_yc |- In(y,s) -> Eq(y,c)

    # Chain: sing_a, sing_c, Eq(y,a) |- Eq(y,c)
    ctx_fwd = [sing_a, sing_c, eq_ya]
    got_iff_ya = _weaken_to(inst_a, ctx_fwd, [iff_ya])
    got_ya_to_in = _cut(got_iff_ya, ya_to_in, iff_ya, ctx_fwd, [Implies(eq_ya, in_ys)])
    got_in = _apply_imp(got_ya_to_in, _axiom(eq_ya, left=[sing_a, sing_c]), ctx_fwd)
    # ctx_fwd |- In(y,s)

    got_iff_yc = _weaken_to(inst_c, ctx_fwd, [iff_yc])
    got_in_to_yc = _cut(got_iff_yc, in_to_yc, iff_yc, ctx_fwd, [Implies(in_ys, eq_yc)])
    got_yc = _apply_imp(got_in_to_yc, got_in, ctx_fwd)
    # [sing_a, sing_c, Eq(y,a)] |- [Eq(y,c)]
    fwd_impl = _implies_right(got_yc)
    # [sing_a, sing_c] |- [Implies(Eq(y,a), Eq(y,c))]

    # Backward: Eq(y,c) -> In(y,s) -> Eq(y,a)
    yc_to_in = iff_elim_right(in_ys, eq_yc)  # iff_yc |- Eq(y,c) -> In(y,s)
    in_to_ya = iff_elim_left(in_ys, eq_ya)    # iff_ya |- In(y,s) -> Eq(y,a)

    ctx_bwd = [sing_a, sing_c, eq_yc]
    got_iff_ya2 = _weaken_to(
        _forall_left(_axiom(iff_ya), sing_a, y), ctx_bwd, [iff_ya])
    got_iff_yc2 = _weaken_to(
        _forall_left(_axiom(iff_yc), sing_c, y), ctx_bwd, [iff_yc])

    got_yc_to_in = _cut(got_iff_yc2, yc_to_in, iff_yc, ctx_bwd, [Implies(eq_yc, in_ys)])
    got_in2 = _apply_imp(got_yc_to_in, _axiom(eq_yc, left=[sing_a, sing_c]), ctx_bwd)

    got_in_to_ya = _cut(got_iff_ya2, in_to_ya, iff_ya, ctx_bwd, [Implies(in_ys, eq_ya)])
    got_ya = _apply_imp(got_in_to_ya, got_in2, ctx_bwd)
    bwd_impl = _implies_right(got_ya)
    # [sing_a, sing_c] |- [Implies(Eq(y,c), Eq(y,a))]

    # iff_intro: [sing_a, sing_c] |- Iff(Eq(y,a), Eq(y,c))
    ii = iff_intro(eq_ya, eq_yc)
    imp_fwd = Implies(eq_ya, eq_yc)
    imp_bwd = Implies(eq_yc, eq_ya)
    ctx_ii = [sing_a, sing_c]
    ii_w = _weaken_to(ii, ctx_ii + [imp_fwd, imp_bwd], [Iff(eq_ya, eq_yc)])
    r1 = _cut(fwd_impl, ii_w, imp_fwd, ctx_ii + [imp_bwd], [Iff(eq_ya, eq_yc)])
    r2 = _cut(bwd_impl, r1, imp_bwd, ctx_ii, [Iff(eq_ya, eq_yc)])
    case_a = _forall_right(r2, y)
    # [sing_a, sing_c] |- H_sing
    case_a_imp = _implies_right(case_a)
    # [sing_a] |- Implies(sing_c, H_sing)

    # Step 3 Case B: sing_a, pair_cd |- H_sing
    # For any z: Eq(z,a) iff Or(Eq(z,c), Eq(z,d))
    # Instantiate z=c: Eq(c,a) iff Or(Eq(c,c), Eq(c,d)). Eq(c,c) true → Eq(c,a) true → a=c.
    # Then H_sing from eq_transfer.

    eq_za = Eq(z, a)
    or_zcd = Or(Eq(z, c), Eq(z, d))
    iff_za_or = Iff(eq_za, or_zcd)

    # From sing_a and pair_cd, derive forall z. Iff(Eq(z,a), Or(Eq(z,c), Eq(z,d)))
    # Same pattern as case A: through In(z,s)
    iff_za_ins = Iff(In(z, s), eq_za)
    iff_or_ins = Iff(In(z, s), or_zcd)

    inst_a2 = _forall_left(_axiom(iff_za_ins), sing_a, z)  # sing_a |- iff_za_ins
    inst_cd = _forall_left(_axiom(iff_or_ins), pair_cd, z)  # pair_cd |- iff_or_ins

    # Forward: Eq(z,a) -> In(z,s) -> Or(Eq(z,c),Eq(z,d))
    ctx_b_fwd = [sing_a, pair_cd, eq_za]
    za_to_in = iff_elim_right(In(z, s), eq_za)
    in_to_or = iff_elim_left(In(z, s), or_zcd)

    ga2 = _weaken_to(inst_a2, ctx_b_fwd, [iff_za_ins])
    ga3 = _cut(ga2, za_to_in, iff_za_ins, ctx_b_fwd, [Implies(eq_za, In(z, s))])
    got_in_b = _apply_imp(ga3, _axiom(eq_za, left=[sing_a, pair_cd]), ctx_b_fwd)

    gc2 = _weaken_to(inst_cd, ctx_b_fwd, [iff_or_ins])
    gc3 = _cut(gc2, in_to_or, iff_or_ins, ctx_b_fwd, [Implies(In(z, s), or_zcd)])
    got_or_b = _apply_imp(gc3, got_in_b, ctx_b_fwd)
    fwd_b = _implies_right(got_or_b)
    # [sing_a, pair_cd] |- Implies(Eq(z,a), Or(Eq(z,c),Eq(z,d)))

    # Backward: Or(Eq(z,c),Eq(z,d)) -> In(z,s) -> Eq(z,a)
    ctx_b_bwd = [sing_a, pair_cd, or_zcd]
    or_to_in = iff_elim_right(In(z, s), or_zcd)
    in_to_za = iff_elim_left(In(z, s), eq_za)

    gc4 = _weaken_to(
        _forall_left(_axiom(iff_or_ins), pair_cd, z), ctx_b_bwd, [iff_or_ins])
    gc5 = _cut(gc4, or_to_in, iff_or_ins, ctx_b_bwd, [Implies(or_zcd, In(z, s))])
    got_in_b2 = _apply_imp(gc5, _axiom(or_zcd, left=[sing_a, pair_cd]), ctx_b_bwd)

    ga4 = _weaken_to(
        _forall_left(_axiom(iff_za_ins), sing_a, z), ctx_b_bwd, [iff_za_ins])
    ga5 = _cut(ga4, in_to_za, iff_za_ins, ctx_b_bwd, [Implies(In(z, s), eq_za)])
    got_za_b = _apply_imp(ga5, got_in_b2, ctx_b_bwd)
    bwd_b = _implies_right(got_za_b)
    # [sing_a, pair_cd] |- Implies(Or(Eq(z,c),Eq(z,d)), Eq(z,a))

    # iff_intro
    ii_b = iff_intro(eq_za, or_zcd)
    imp_fwd_b = Implies(eq_za, or_zcd)
    imp_bwd_b = Implies(or_zcd, eq_za)
    ctx_b = [sing_a, pair_cd]
    ii_bw = _weaken_to(ii_b, ctx_b + [imp_fwd_b, imp_bwd_b], [iff_za_or])
    rb1 = _cut(fwd_b, ii_bw, imp_fwd_b, ctx_b + [imp_bwd_b], [iff_za_or])
    rb2 = _cut(bwd_b, rb1, imp_bwd_b, ctx_b, [iff_za_or])
    got_iff_b = _forall_right(rb2, z)
    # [sing_a, pair_cd] |- Forall(z, Iff(Eq(z,a), Or(Eq(z,c),Eq(z,d))))

    # Instantiate z=c: Iff(Eq(c,a), Or(Eq(c,c), Eq(c,d)))
    eq_ca = Eq(c, a)
    eq_cc = Eq(c, c)
    eq_cd_var = Eq(c, d)
    or_cc_cd = Or(eq_cc, eq_cd_var)
    iff_ca_or = Iff(eq_ca, or_cc_cd)

    got_iff_b_body = got_iff_b.sequent.right[0]  # Forall(z, ...)
    inst_zc = _forall_left(_axiom(iff_ca_or), got_iff_b_body, c)
    got_iff_ca = _cut(got_iff_b, inst_zc, got_iff_b_body, ctx_b, [iff_ca_or])
    # [sing_a, pair_cd] |- Iff(Eq(c,a), Or(Eq(c,c), Eq(c,d)))

    # Eq(c,c) true → Or(Eq(c,c), Eq(c,d)) true
    got_cc = _instantiate(eq_reflexive(), [c])
    got_or_cc = _cut(got_cc, or_intro_left(eq_cc, eq_cd_var), eq_cc, [], [or_cc_cd])
    # |- Or(Eq(c,c), Eq(c,d))

    # Apply iff backward: Eq(c,a)
    got_ca = _apply_imp(
        iff_elim_right(eq_ca, or_cc_cd),
        _axiom(or_cc_cd, left=[iff_ca_or]),
        [iff_ca_or, or_cc_cd])
    s_ca1 = _cut(got_iff_ca, got_ca, iff_ca_or, ctx_b + [or_cc_cd], [eq_ca])
    s_ca2 = _cut(got_or_cc, s_ca1, or_cc_cd, ctx_b, [eq_ca])
    # [sing_a, pair_cd] |- Eq(c,a) → a=c by symmetry

    # Eq(c,a) → Eq(a,c)
    sym_ca = _instantiate(eq_symmetric(), [c, a])
    got_ac = _apply_imp(sym_ca, s_ca2, ctx_b)
    # [sing_a, pair_cd] |- Eq(a,c)

    # From Eq(a,c), derive H_sing via eq_transfer
    et = _instantiate(eq_transfer(), [a, c, y])  # |- Eq(a,c) -> Iff(Eq(y,a), Eq(y,c))
    got_iff_yac = _apply_imp(et, got_ac, ctx_b)
    # [sing_a, pair_cd] |- Iff(Eq(y,a), Eq(y,c))
    got_hsing_b = _forall_right(got_iff_yac, y)
    # [sing_a, pair_cd] |- Forall(y, Iff(Eq(y,a), Eq(y,c))) = H_sing

    case_b_imp = _implies_right(got_hsing_b)
    # [sing_a] |- Implies(pair_cd, H_sing)

    # Step 4: or_elim on Or(sing_c, pair_cd) with both cases giving H_sing
    oe = or_elim(sing_c, pair_cd, H_sing)
    ctx_oe = [H_tuple, sing_a]
    imp_sc = Implies(sing_c, H_sing)
    imp_pcd = Implies(pair_cd, H_sing)

    oe_w = _weaken_to(oe, ctx_oe + [or_right, imp_sc, imp_pcd], [H_sing])
    s2_w = _weaken_to(s2, ctx_oe, [or_right])
    case_a_w = _weaken_to(case_a_imp, ctx_oe, [imp_sc])
    case_b_w = _weaken_to(case_b_imp, ctx_oe, [imp_pcd])

    t1 = _cut(s2_w, oe_w, or_right, ctx_oe + [imp_sc, imp_pcd], [H_sing])
    t2 = _cut(case_a_w, t1, imp_sc, ctx_oe + [imp_pcd], [H_sing])
    t3 = _cut(case_b_w, t2, imp_pcd, ctx_oe, [H_sing])
    # [H_tuple, sing_a] |- H_sing

    # Close: H_sing doesn't depend on s, so we can close sing_a with implies_right
    # and forall_right on s (s only appears in sing_a, not H_sing)
    t4 = _implies_right(t3)
    # [H_tuple] |- Implies(sing_a, H_sing)
    t5 = _forall_right(t4, s)
    # [H_tuple] |- Forall(s, Implies(sing_a, H_sing))

    # Now we need: from Forall(s, Implies(sing_a, H_sing)) and exists s. sing_a, get H_sing.
    # For now, return the universal form — the existential step needs pairing axiom.
    t6 = _implies_right(t5)
    t7 = _forall_right(t6, d)
    t8 = _forall_right(t7, c)
    t9 = _forall_right(t8, b)
    t10 = _forall_right(t9, a)
    t10.name = 'singleton_from_tuple'
    return t10


def forall_implies_exists(P_body, Q, var):
    """Forall(var, Implies(P_body, Q)), Not(Forall(var, Not(P_body))) |- Q
    From 'for all x, P(x) implies Q' and 'exists x with P(x)', derive Q.
    Q must not contain var free. P_body has var free."""
    # Exists(var, P_body) = Not(Forall(var, Not(P_body)))
    FA_imp = Forall(var, Implies(P_body, Q))
    FA_not = Forall(var, Not(P_body))
    EX = Not(FA_not)  # Exists(var, P_body)

    # Classical proof:
    # FA_imp, EX |- Q
    # Assume not(Q), derive contradiction with EX.
    # From not(Q) and FA_imp: for all x, P(x) implies Q, and not(Q),
    # so for all x, not(P(x)). So Forall(var, Not(P_body)). Contradicts EX.

    NQ = Not(Q)
    NP = Not(P_body)
    imp_PQ = Implies(P_body, Q)

    # FA_imp |- imp_PQ (forall_left, term=var)
    inst = _forall_left(_axiom(imp_PQ), FA_imp, var)

    # imp_PQ, NQ |- NP
    # implies_left on imp_PQ: NQ |- P_body, NP and NQ, Q |- NP
    #   p0: NQ |- P_body, NP... hmm, need P_body first on right.
    #   Actually: imp_PQ = Implies(P_body, Q).
    #   implies_left: from [NQ] |- [P_body, NP] and [NQ, Q] |- [NP]
    #   result: [NQ, imp_PQ] |- [NP]

    # [NQ] |- [P_body, NP]: we need P_body first. Just put NP as weakening.
    # Actually we can't prove [NQ] |- [P_body] in general. Need classical reasoning.

    # Better: [NQ, imp_PQ] |- [NP]
    # not_right: [NQ, imp_PQ, P_body] |- []
    # implies_left on imp_PQ: [NQ, P_body] |- [P_body] and [NQ, P_body, Q] |- []
    #   p0: [NQ, P_body] |- [P_body]: axiom ✓
    #   p1: [NQ, P_body, Q] |- []: exchange [NQ, Q, P_body]... wait.
    #     not_left on NQ (last needs NQ last): exchange to [P_body, Q, NQ] |- []
    #     premise: [P_body, Q] |- [Q]: axiom ✓
    p0 = _axiom(P_body, left=[NQ])
    p1_ax = _axiom(Q, left=[P_body])
    p1_nl = _not_left(p1_ax)  # [P_body, Q, NQ] |- []
    p1 = _exchange_left(p1_nl, [NQ, P_body, Q])
    impl = _implies_left(p0, p1)  # [NQ, P_body, imp_PQ] |- []
    impl_x = _exchange_left(impl, [NQ, imp_PQ, P_body])
    got_np = _not_right(impl_x)  # [NQ, imp_PQ] |- [NP]

    # From FA_imp: forall_left gives imp_PQ. Cut:
    # FA_imp, NQ |- NP
    got_np2 = _cut(inst, got_np, imp_PQ, [FA_imp, NQ], [NP])

    # forall_right on var: FA_imp, NQ |- Forall(var, NP) = FA_not
    got_fa_not = _forall_right(got_np2, var)
    # FA_imp, NQ |- FA_not

    # not_left on EX = Not(FA_not): from FA_imp, NQ |- FA_not derive FA_imp, NQ, EX |-
    # not_left expects FA_not first on right ✓
    got_contra = _not_left(got_fa_not)  # [FA_imp, NQ, EX] |- []

    # not_right: [FA_imp, EX] |- [Not(NQ)] = [FA_imp, EX] |- [Not(Not(Q))]
    got_contra_x = _exchange_left(got_contra, [FA_imp, EX, NQ])
    got_nnq = _not_right(got_contra_x)  # [FA_imp, EX] |- [Not(NQ)]

    # Double negation elimination: Not(Not(Q)) |- Q (classical)
    # not_left on Not(Q): from |- Q, ... derive Not(Q), ... |-
    # Actually: Not(Not(Q)) |- Q in classical sequent calculus:
    # not_left: from |- Not(Q) derive Not(Not(Q)) |-... no.
    # Cut: |- Q, Not(Q) (axiom-like from not_right on [Q] |- [Q])
    # and Not(Q), Not(Not(Q)) |- (not_left on Not(Not(Q)): from Not(Q) |- Not(Q))

    # Q |- Q (axiom). not_right: |- Not(Q), Q. exchange: |- Q, Not(Q).
    ax_q = _axiom(Q)
    dn_r = _not_right(ax_q)  # [] |- [Not(Q), Q]... wait
    # _not_right: last on left is Q, first on right becomes Not(Q).
    # [Q] |- [], not_right: [] |- [Not(Q)]... no, there's nothing on left after removing Q.
    # Hmm, I need [] |- [Q, Not(Q)] for the cut.

    # axiom: [Q] |- [Q]. not_left on Not(Q): from [Q] |- [Q] derive [Q, Not(Q)] |- []
    # Hmm, that removes Q from right.

    # Classical double negation: Not(Not(Q)) |- Q
    # Proof: axiom Q |- Q. weaken right: Q |- Q, Not(Q).
    # exchange right: Q |- Not(Q), Q... wait weakening adds first.
    # Q |- Q (axiom). weakening_right: Q |- Not(Q), Q. (Not(Q) added first)
    # not_left: Q, Not(Not(Q)) |- Q. (Not(Not(Q)) last, premise Q |- Not(Q), Q)
    # exchange: Not(Not(Q)), Q |- Q... hmm.

    # Actually: _not_left takes premise G |- A, D and makes G, Not(A) |- D.
    # premise: [Q] |- [Not(Q), Q]... Not(Q) first on right ✓.
    # result: [Q, Not(Not(Q))] |- [Q]. Not(Not(Q)) last ✓.

    ax_q2 = _axiom(Q)  # [Q] |- [Q]
    wk = Proof(Sequent([Q], [Not(Q), Q]), 'weakening_right', [ax_q2])
    dn_step = _not_left(wk)  # [Q, Not(Not(Q))] |- [Q]
    dn = _exchange_left(dn_step, [Not(Not(Q)), Q])
    # [Not(Not(Q)), Q] |- [Q]... still has Q on left.

    # I need Not(Not(Q)) |- Q without Q on left.
    # Cut: Not(Not(Q)) |- Q, Not(Q) and Not(Not(Q)), Q |- Q => Not(Not(Q)) |- Q
    # p0: Not(Not(Q)) |- Q, Not(Q)
    #   not_right: Not(Not(Q)), Q |- Not(Q)... nope, Q not on right.
    #   Hmm. Let me try:
    #   axiom: [Not(Q)] |- [Not(Q)]. weakening_right: [Not(Q)] |- [Q, Not(Q)].
    #   exchange: [Not(Q)] |- [Not(Q), Q].
    #   not_left: [Not(Q), Not(Not(Q))] |- [Q].
    #   exchange: [Not(Not(Q)), Not(Q)] |- [Q].
    #   implies_right? No...

    # Fresh approach for double negation elimination:
    # [Not(Not(Q))] |- [Q]
    # By not_right: [Not(Not(Q)), Not(Q)] |- [] ... wait, that gives |- Not(Not(Q)), but wrong direction.

    # Classical: [Not(Not(Q))] |- [Q]
    # not_left on Not(Not(Q)) (last): premise |- [Not(Q)]
    # But we need |- [Not(Q), Q] for premise with D=[Q].
    # premise: [] |- [Not(Q), Q]. This is provable:
    # axiom [Q] |- [Q]. implies_right... no. weakening_right on empty?
    # We need Q on right without it on left. Classical tautology.
    # not_right: [Q] |- []. Then [] |- [Not(Q)].
    # Hmm [Q] |- [] is not provable.

    # [] |- [Not(Q), Q]: not_right from [Q] |- [Q] gives [] |- [Not(Q), Q]?
    # _not_right: last on left is Q, first on right is Q. Result: [] |- [Not(Q), Q]... wait:
    # [Q] |- [Q]. _not_right takes last on left (Q), wraps as Not(Q) first on right.
    # Result: [] |- [Not(Q), Q]. Remaining right: original right = [Q], so [Not(Q)] + [Q] = [Not(Q), Q]. ✓!

    p_lem = _not_right(_axiom(Q))  # [] |- [Not(Q), Q]  (excluded middle / law of excluded third)

    # not_left: from [] |- [Not(Q), Q] derive [Not(Not(Q))] |- [Q]
    # Not(Not(Q)) last on left ✓. Premise right: [Not(Q), Q]. Not(Q) first ✓.
    dne = _not_left(p_lem)  # [Not(Not(Q))] |- [Q]

    # Cut: [FA_imp, EX] |- [Q]
    # got_nnq: [FA_imp, EX] |- [Not(Not(Q))]
    result = _cut(got_nnq, dne, Not(Not(Q)), [FA_imp, EX], [Q])

    result.name = 'forall_implies_exists'
    return result


def kuratowski():
    """Kuratowski tuple injection composing singleton_from_tuple + tuple_injection_full.
    Hypotheses: H_tuple (outer pair eq), Exists(s, sing_a_s), H_pair (inner pair eq).
    Conclusion: And(Eq(a,c), Eq(b,d))."""
    a, b, c, d = Var(), Var(), Var(), Var()
    x, y, s, z = Var(), Var(), Var(), Var()

    sing_a_s = Forall(z, Iff(In(z, s), Eq(z, a)))
    H_sing = Forall(y, Iff(Eq(y, a), Eq(y, c)))
    EX_sing = Not(Forall(s, Not(sing_a_s)))

    sft = singleton_from_tuple(a, b, c, d)
    sft_inst = _instantiate(sft, [a, b, c, d])
    H_tuple = sft_inst.sequent.right[0].left
    got_fa = _apply_imp(sft_inst, _axiom(H_tuple), [H_tuple])

    fie = forall_implies_exists(sing_a_s, H_sing, s)
    got_hsing = _cut(got_fa, fie,
                     Forall(s, Implies(sing_a_s, H_sing)),
                     [H_tuple, EX_sing], [H_sing])

    eq_xa, eq_xb = Eq(x, a), Eq(x, b)
    eq_xc, eq_xd = Eq(x, c), Eq(x, d)
    H_pair = Forall(x, Iff(Or(eq_xa, eq_xb), Or(eq_xc, eq_xd)))

    tif = _instantiate(tuple_injection_full(), [a, b, c, d])
    tif1 = _apply_imp(tif, _axiom(H_pair), [H_pair])

    ctx = [H_tuple, EX_sing, H_pair]
    tif2 = _apply_imp(tif1, _weaken_to(got_hsing, ctx, [H_sing]), ctx)

    s_i1 = _implies_right(tif2)
    s_i2 = _implies_right(s_i1)
    s_i3 = _implies_right(s_i2)
    s_fd = _forall_right(s_i3, d)
    s_fc = _forall_right(s_fd, c)
    s_fb = _forall_right(s_fc, b)
    s_fa = _forall_right(s_fb, a)
    s_fa.name = 'kuratowski'
    return s_fa
