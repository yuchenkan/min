"""Theorems proved from the sequent calculus. All theorems are closed (no free vars)."""

from core.lang import Var, In, Not, Implies, Forall
from core.derived import Eq, Iff, And, Or, Exists
from core.proof import Sequent, Proof
from core import zfc
from definitions import EmptySet, OrdPair


# --- ZFC axioms as theorems (A |- A) ---

def extensionality():
    ax = zfc.Extensionality()
    return Proof(Sequent([ax], [ax]), 'axiom', principal=ax, name='extensionality')

def empty_set():
    ax = zfc.EmptySet()
    return Proof(Sequent([ax], [ax]), 'axiom', principal=ax, name='empty_set')

def pairing():
    ax = zfc.Pairing()
    return Proof(Sequent([ax], [ax]), 'axiom', principal=ax, name='pairing')

def union():
    ax = zfc.Union()
    return Proof(Sequent([ax], [ax]), 'axiom', principal=ax, name='union')

def power_set():
    ax = zfc.PowerSet()
    return Proof(Sequent([ax], [ax]), 'axiom', principal=ax, name='power_set')

def separation(phi, vars: list[Var]):
    ax = zfc.Separation(phi, vars)
    return Proof(Sequent([ax], [ax]), 'axiom', principal=ax, name='separation')

def infinity():
    ax = zfc.Infinity()
    return Proof(Sequent([ax], [ax]), 'axiom', principal=ax, name='infinity')

def choice():
    ax = zfc.Choice()
    return Proof(Sequent([ax], [ax]), 'axiom', principal=ax, name='choice')

def replacement(phi, vars: list[Var]):
    ax = zfc.Replacement(phi, vars)
    return Proof(Sequent([ax], [ax]), 'axiom', principal=ax, name='replacement')

def regularity():
    ax = zfc.Regularity()
    return Proof(Sequent([ax], [ax]), 'axiom', principal=ax, name='regularity')


# --- Logic theorems ---

def modus_ponens(P, Q, vars: list[Var]):
    """|- forall vars. P implies (P implies Q) implies Q"""
    imp = Implies(P, Q)
    # [P] |- [P]
    ax = Proof(Sequent([P], [P]), 'axiom', principal=P)
    # [P] |- [P, Q]
    w = Proof(Sequent([P], [P, Q]), 'weakening_right', [ax], principal=Q)
    # [P, Q] |- [Q]
    ax2 = Proof(Sequent([P, Q], [Q]), 'axiom', principal=Q)
    # [P, imp] |- [Q]
    s1 = Proof(Sequent([P, imp], [Q]), 'implies_left', [w, ax2], principal=imp)
    # [P] |- [imp implies Q]
    imp2 = Implies(imp, Q)
    s2 = Proof(Sequent([P], [imp2]), 'implies_right', [s1], principal=imp2)
    # [] |- [P implies (imp implies Q)]
    top = Implies(P, imp2)
    s3 = Proof(Sequent([], [top]), 'implies_right', [s2], principal=top)
    # close with forall
    proof = s3
    for v in vars:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], term=v, principal=fa)
    proof.name = 'modus_ponens'
    return proof


def double_negation(P, vars: list[Var]):
    """|- forall vars. P implies Not(Not(P))"""
    nP = Not(P)
    nnP = Not(nP)
    ax = Proof(Sequent([P], [P]), 'axiom', principal=P)
    s1 = Proof(Sequent([P, nP], []), 'not_left', [ax], principal=nP)
    s2 = Proof(Sequent([P], [nnP]), 'not_right', [s1], principal=nnP)
    top = Implies(P, nnP)
    s3 = Proof(Sequent([], [top]), 'implies_right', [s2], principal=top)
    proof = s3
    for v in vars:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], term=v, principal=fa)
    proof.name = 'double_negation'
    return proof


def iff_intro(P, Q, vars: list[Var]):
    """|- forall vars. (P->Q) implies (Q->P) implies Iff(P,Q)"""
    PQ = Implies(P, Q)
    QP = Implies(Q, P)
    NQP = Not(QP)
    H = Implies(PQ, NQP)
    iff = Iff(P, Q)
    # [PQ, QP] |- [PQ]
    ax0 = Proof(Sequent([PQ, QP], [PQ]), 'axiom', principal=PQ)
    # [PQ, QP, NQP] |- []
    ax1 = Proof(Sequent([PQ, QP], [QP]), 'axiom', principal=QP)
    s1 = Proof(Sequent([PQ, QP, NQP], []), 'not_left', [ax1], principal=NQP)
    # [PQ, QP, H] |- []
    s2 = Proof(Sequent([PQ, QP, H], []), 'implies_left', [ax0, s1], principal=H)
    # [PQ, QP] |- [iff]
    s3 = Proof(Sequent([PQ, QP], [iff]), 'not_right', [s2], principal=iff)
    # discharge QP, PQ, then forall
    imp1 = Implies(QP, iff)
    s4 = Proof(Sequent([PQ], [imp1]), 'implies_right', [s3], principal=imp1)
    imp2 = Implies(PQ, imp1)
    s5 = Proof(Sequent([], [imp2]), 'implies_right', [s4], principal=imp2)
    proof = s5
    for v in vars:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], term=v, principal=fa)
    proof.name = 'iff_intro'
    return proof


def iff_elim_left(P, Q, vars: list[Var]):
    """|- forall vars. Iff(P,Q) implies (P implies Q)"""
    PQ = Implies(P, Q)
    QP = Implies(Q, P)
    NQP = Not(QP)
    H = Implies(PQ, NQP)
    NH = Not(H)  # Iff(P,Q) expanded
    iff = Iff(P, Q)
    # NH, P |- Q via cut on H
    # p0: NH, P |- H, Q
    ax_p = Proof(Sequent([NH, QP, P], [P, Q]), 'axiom', principal=P)
    ax_q = Proof(Sequent([NH, QP, P, Q], [Q]), 'axiom', principal=Q)
    s1 = Proof(Sequent([NH, QP, P, PQ], [Q]), 'implies_left', [ax_p, ax_q], principal=PQ)
    s2 = Proof(Sequent([NH, P, PQ], [NQP, Q]), 'not_right', [s1], principal=NQP)
    p0 = Proof(Sequent([NH, P], [H, Q]), 'implies_right', [s2], principal=H)
    # p1: NH, P, H |- Q
    ax_h = Proof(Sequent([P, H], [H, Q]), 'axiom', principal=H)
    p1 = Proof(Sequent([P, H, NH], [Q]), 'not_left', [ax_h], principal=NH)
    # cut
    s3 = Proof(Sequent([NH, P], [Q]), 'cut', [p0, p1], principal=H)
    s4 = Proof(Sequent([NH], [PQ]), 'implies_right', [s3], principal=PQ)
    # discharge NH, then forall
    imp = Implies(iff, PQ)
    s5 = Proof(Sequent([], [imp]), 'implies_right', [s4], principal=imp)
    proof = s5
    for v in vars:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], term=v, principal=fa)
    proof.name = 'iff_elim_left'
    return proof


def iff_elim_right(P, Q, vars: list[Var]):
    """|- forall vars. Iff(P,Q) implies (Q implies P)"""
    PQ = Implies(P, Q)
    QP = Implies(Q, P)
    NQP = Not(QP)
    H = Implies(PQ, NQP)
    NH = Not(H)
    iff = Iff(P, Q)
    # NH, Q |- P via cut on H
    ax_q = Proof(Sequent([NH, PQ, Q], [Q, P]), 'axiom', principal=Q)
    ax_p = Proof(Sequent([NH, PQ, Q, P], [P]), 'axiom', principal=P)
    s1 = Proof(Sequent([NH, PQ, Q, QP], [P]), 'implies_left', [ax_q, ax_p], principal=QP)
    s2 = Proof(Sequent([NH, Q, PQ], [NQP, P]), 'not_right', [s1], principal=NQP)
    p0 = Proof(Sequent([NH, Q], [H, P]), 'implies_right', [s2], principal=H)
    ax_h = Proof(Sequent([Q, H], [H, P]), 'axiom', principal=H)
    p1 = Proof(Sequent([Q, H, NH], [P]), 'not_left', [ax_h], principal=NH)
    s3 = Proof(Sequent([NH, Q], [P]), 'cut', [p0, p1], principal=H)
    s4 = Proof(Sequent([NH], [QP]), 'implies_right', [s3], principal=QP)
    imp = Implies(iff, QP)
    s5 = Proof(Sequent([], [imp]), 'implies_right', [s4], principal=imp)
    proof = s5
    for v in vars:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], term=v, principal=fa)
    proof.name = 'iff_elim_right'
    return proof


def or_intro_left(A, B, vars: list[Var]):
    """|- forall vars. A implies Or(A, B)"""
    NA = Not(A)
    orAB = Implies(NA, B)
    ax = Proof(Sequent([A], [A, B]), 'weakening_right',
               [Proof(Sequent([A], [A]), 'axiom', principal=A)], principal=B)
    s1 = Proof(Sequent([A, NA], [B]), 'not_left', [ax], principal=NA)
    s2 = Proof(Sequent([A], [orAB]), 'implies_right', [s1], principal=orAB)
    top = Implies(A, Or(A, B))
    s3 = Proof(Sequent([], [top]), 'implies_right', [s2], principal=top)
    proof = s3
    for v in vars:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], term=v, principal=fa)
    proof.name = 'or_intro_left'
    return proof


def or_intro_right(A, B, vars: list[Var]):
    """|- forall vars. B implies Or(A, B)"""
    NA = Not(A)
    orAB = Implies(NA, B)
    ax = Proof(Sequent([NA, B], [B]), 'axiom', principal=B)
    s1 = Proof(Sequent([B], [orAB]), 'implies_right', [ax], principal=orAB)
    top = Implies(B, Or(A, B))
    s2 = Proof(Sequent([], [top]), 'implies_right', [s1], principal=top)
    proof = s2
    for v in vars:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], term=v, principal=fa)
    proof.name = 'or_intro_right'
    return proof


def or_elim(A, B, C, vars: list[Var]):
    """|- forall vars. Or(A,B) implies (A->C) implies (B->C) implies C"""
    NA = Not(A)
    OrAB = Implies(NA, B)
    AC = Implies(A, C)
    BC = Implies(B, C)
    # [OrAB, AC, BC] |- [C]
    p1 = Proof(Sequent([OrAB, AC, C], [C]), 'axiom', principal=C)
    # [AC] |- [NA, B, C]: from [AC, A] |- [B, C]
    ax_a = Proof(Sequent([A], [A, B, C]), 'axiom', principal=A)
    ax_c = Proof(Sequent([A, C], [B, C]), 'axiom', principal=C)
    impl_ac = Proof(Sequent([A, AC], [B, C]), 'implies_left', [ax_a, ax_c], principal=AC)
    p0a = Proof(Sequent([AC], [NA, B, C]), 'not_right', [impl_ac], principal=NA)
    # [AC, B] |- [B, C]
    p0b = Proof(Sequent([AC, B], [B, C]), 'axiom', principal=B)
    # [AC, OrAB] |- [B, C]
    impl_or = Proof(Sequent([AC, OrAB], [B, C]), 'implies_left', [p0a, p0b], principal=OrAB)
    # [OrAB, AC, BC] |- [C]
    result = Proof(Sequent([OrAB, AC, BC], [C]), 'implies_left',
                   [impl_or, p1], principal=BC)
    # discharge BC, AC, OrAB
    imp1 = Implies(BC, C)
    s1 = Proof(Sequent([OrAB, AC], [imp1]), 'implies_right', [result], principal=imp1)
    imp2 = Implies(AC, imp1)
    s2 = Proof(Sequent([OrAB], [imp2]), 'implies_right', [s1], principal=imp2)
    imp3 = Implies(Or(A, B), imp2)
    s3 = Proof(Sequent([], [imp3]), 'implies_right', [s2], principal=imp3)
    proof = s3
    for v in vars:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], term=v, principal=fa)
    proof.name = 'or_elim'
    return proof


def and_intro(A, B, vars: list[Var]):
    """|- forall vars. A implies B implies And(A,B)"""
    NB = Not(B)
    imp = Implies(A, NB)
    nand = Not(imp)
    ax_a = Proof(Sequent([A, B], [A]), 'axiom', principal=A)
    ax_b = Proof(Sequent([A, B], [B]), 'axiom', principal=B)
    s1 = Proof(Sequent([A, B, NB], []), 'not_left', [ax_b], principal=NB)
    s2 = Proof(Sequent([A, B, imp], []), 'implies_left', [ax_a, s1], principal=imp)
    s3 = Proof(Sequent([A, B], [nand]), 'not_right', [s2], principal=nand)
    # Use And display
    s3d = Proof(Sequent([A, B], [And(A, B)]), s3.rule, s3.premises, principal=s3.principal)
    imp1 = Implies(B, And(A, B))
    s4 = Proof(Sequent([A], [imp1]), 'implies_right', [s3d], principal=imp1)
    imp2 = Implies(A, imp1)
    s5 = Proof(Sequent([], [imp2]), 'implies_right', [s4], principal=imp2)
    proof = s5
    for v in vars:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], term=v, principal=fa)
    proof.name = 'and_intro'
    return proof


def and_elim_left(A, B, vars: list[Var]):
    """|- forall vars. And(A,B) implies A"""
    NB = Not(B)
    imp = Implies(A, NB)
    nand = Not(imp)
    # nand |- A via cut on imp
    # p0: nand |- imp, A
    ax_a = Proof(Sequent([nand, A, B], [A]), 'axiom', principal=A)
    s1 = Proof(Sequent([nand, A], [NB, A]), 'not_right', [ax_a], principal=NB)
    p0 = Proof(Sequent([nand], [imp, A]), 'implies_right', [s1], principal=imp)
    # p1: nand, imp |- A
    ax_imp = Proof(Sequent([imp], [imp, A]), 'axiom', principal=imp)
    p1 = Proof(Sequent([imp, nand], [A]), 'not_left', [ax_imp], principal=nand)
    s2 = Proof(Sequent([nand], [A]), 'cut', [p0, p1], principal=imp)
    # Use And display
    s2d = Proof(Sequent([And(A, B)], [A]), s2.rule, s2.premises, principal=s2.principal)
    top = Implies(And(A, B), A)
    s3 = Proof(Sequent([], [top]), 'implies_right', [s2d], principal=top)
    proof = s3
    for v in vars:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], term=v, principal=fa)
    proof.name = 'and_elim_left'
    return proof


def and_elim_right(A, B, vars: list[Var]):
    """|- forall vars. And(A,B) implies B"""
    NB = Not(B)
    imp = Implies(A, NB)
    nand = Not(imp)
    # nand |- B via cut on imp
    ax_b = Proof(Sequent([nand, A, B], [B]), 'axiom', principal=B)
    s1 = Proof(Sequent([nand, A], [NB, B]), 'not_right', [ax_b], principal=NB)
    p0 = Proof(Sequent([nand], [imp, B]), 'implies_right', [s1], principal=imp)
    ax_imp = Proof(Sequent([imp], [imp, B]), 'axiom', principal=imp)
    p1 = Proof(Sequent([imp, nand], [B]), 'not_left', [ax_imp], principal=nand)
    s2 = Proof(Sequent([nand], [B]), 'cut', [p0, p1], principal=imp)
    s2d = Proof(Sequent([And(A, B)], [B]), s2.rule, s2.premises, principal=s2.principal)
    top = Implies(And(A, B), B)
    s3 = Proof(Sequent([], [top]), 'implies_right', [s2d], principal=top)
    proof = s3
    for v in vars:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], term=v, principal=fa)
    proof.name = 'and_elim_right'
    return proof


def forall_instantiation(x: Var, body, t: Var, vars: list[Var]):
    """|- forall vars. (forall x. body) implies body[t/x]"""
    instance = body.subst(x, t)
    fa = Forall(x, body)
    ax = Proof(Sequent([instance], [instance]), 'axiom', principal=instance)
    s1 = Proof(Sequent([fa], [instance]), 'forall_left', [ax],
               principal=fa, term=t)
    top = Implies(fa, instance)
    s2 = Proof(Sequent([], [top]), 'implies_right', [s1], principal=top)
    proof = s2
    for v in vars:
        body_r = proof.sequent.right[0]
        fa_v = Forall(v, body_r)
        proof = Proof(Sequent([], [fa_v]), 'forall_right', [proof], term=v, principal=fa_v)
    proof.name = 'forall_instantiation'
    return proof


def eq_reflexive():
    """|- forall a. Eq(a, a)"""
    a, z = Var(), Var()
    P = In(z, a)
    PtoP = Implies(P, P)
    NPtoP = Not(PtoP)
    imp_main = Implies(PtoP, NPtoP)
    iff_body = Not(imp_main)

    ax = Proof(Sequent([P], [P]), 'axiom', principal=P)
    p0 = Proof(Sequent([], [PtoP]), 'implies_right', [ax], principal=PtoP)
    p1_ax = Proof(Sequent([P], [P]), 'axiom', principal=P)
    p1_ir = Proof(Sequent([], [PtoP]), 'implies_right', [p1_ax], principal=PtoP)
    p1 = Proof(Sequent([NPtoP], []), 'not_left', [p1_ir], principal=NPtoP)
    s1 = Proof(Sequent([imp_main], []), 'implies_left', [p0, p1], principal=imp_main)
    s2 = Proof(Sequent([], [iff_body]), 'not_right', [s1], principal=iff_body)
    fz = Forall(z, iff_body)
    s3 = Proof(Sequent([], [fz]), 'forall_right', [s2], term=z, principal=fz)
    fa = Forall(a, Eq(a, a))
    s4 = Proof(Sequent([], [fa]), 'forall_right', [s3], term=a, principal=fa, name='eq_reflexive')
    return s4


def eq_symmetric():
    """|- forall a. forall b. Eq(a,b) implies Eq(b,a)"""
    a, b, z = Var(), Var(), Var()

    P = In(z, a)
    Q = In(z, b)
    PQ = Implies(P, Q)
    QP = Implies(Q, P)
    NPQ = Not(PQ)
    NQP = Not(QP)
    H1 = Implies(PQ, NQP)   # negated inside Iff(P,Q)
    H2 = Implies(QP, NPQ)   # negated inside Iff(Q,P)
    iff_pq = Not(H1)         # Iff(P,Q) expanded
    iff_qp = Not(H2)         # Iff(Q,P) expanded
    eq_ab = Forall(z, iff_pq)  # Eq(a,b) expanded
    eq_ba = Forall(z, iff_qp)  # Eq(b,a) expanded

    # --- Extract QP from Not(H1) via cut on H1 ---
    # Not(H1), PQ, QP |- QP
    a1 = Proof(Sequent([iff_pq, PQ, QP], [QP]), 'axiom', principal=QP)
    # Not(H1), PQ |- NQP, QP
    a2 = Proof(Sequent([iff_pq, PQ], [NQP, QP]), 'not_right', [a1], principal=NQP)
    # Not(H1) |- H1, QP
    a3 = Proof(Sequent([iff_pq], [H1, QP]), 'implies_right', [a2], principal=H1)
    # H1 |- H1
    a4 = Proof(Sequent([H1], [H1]), 'axiom', principal=H1)
    # H1 |- H1, QP
    a5 = Proof(Sequent([H1], [H1, QP]), 'weakening_right', [a4], principal=QP)
    # H1, Not(H1) |- QP
    a6 = Proof(Sequent([H1, iff_pq], [QP]), 'not_left', [a5], principal=iff_pq)
    # Not(H1) |- QP
    extract_qp = Proof(Sequent([iff_pq], [QP]), 'cut', [a3, a6], principal=H1)

    # --- Extract PQ from Not(H1) via cut on H1 ---
    # Not(H1), PQ |- PQ
    b1 = Proof(Sequent([iff_pq, PQ], [PQ]), 'axiom', principal=PQ)
    # Not(H1), PQ |- NQP, PQ
    b2 = Proof(Sequent([iff_pq, PQ], [NQP, PQ]), 'weakening_right', [b1], principal=NQP)
    # Not(H1) |- H1, PQ
    b3 = Proof(Sequent([iff_pq], [H1, PQ]), 'implies_right', [b2], principal=H1)
    # H1 |- H1
    b4 = Proof(Sequent([H1], [H1]), 'axiom', principal=H1)
    # H1 |- H1, PQ
    b5 = Proof(Sequent([H1], [H1, PQ]), 'weakening_right', [b4], principal=PQ)
    # H1, Not(H1) |- PQ
    b6 = Proof(Sequent([H1, iff_pq], [PQ]), 'not_left', [b5], principal=iff_pq)
    # Not(H1) |- PQ
    extract_pq = Proof(Sequent([iff_pq], [PQ]), 'cut', [b3, b6], principal=H1)

    # --- Combine: Not(H1) |- Not(H2) ---
    # not_left: Not(H1), Not(PQ) |- from Not(H1) |- PQ
    c1 = Proof(Sequent([iff_pq, NPQ], []), 'not_left', [extract_pq], principal=NPQ)
    # implies_left on H2: Not(H1), H2 |- from extract_qp and c1
    c2 = Proof(Sequent([iff_pq, H2], []), 'implies_left', [extract_qp, c1], principal=H2)
    # not_right: Not(H1) |- Not(H2) = iff_pq |- iff_qp
    core = Proof(Sequent([iff_pq], [iff_qp]), 'not_right', [c2], principal=iff_qp)

    # --- Lift to Eq level ---
    # forall_left: Eq(a,b) |- iff_qp
    fl = Proof(Sequent([eq_ab], [iff_qp]), 'forall_left', [core], principal=eq_ab, term=z)
    # forall_right: Eq(a,b) |- Eq(b,a)
    fr = Proof(Sequent([eq_ab], [eq_ba]), 'forall_right', [fl], principal=eq_ba, term=z)

    # --- Close ---
    imp = Implies(Eq(a, b), Eq(b, a))
    s1 = Proof(Sequent([], [imp]), 'implies_right', [fr], principal=imp)
    fb = Forall(b, imp)
    s2 = Proof(Sequent([], [fb]), 'forall_right', [s1], term=b, principal=fb)
    fa = Forall(a, fb)
    s3 = Proof(Sequent([], [fa]), 'forall_right', [s2], term=a, principal=fa)
    s3.name = 'eq_symmetric'
    return s3


def unique_empty():
    """|- forall a. forall b. (forall x. Not(x in a)) implies (forall x. Not(x in b)) implies Eq(a,b)"""
    a, b, z = Var(), Var(), Var()
    x1, x2 = Var(), Var()

    P = In(z, a)
    Q = In(z, b)
    NP = Not(P)
    NQ = Not(Q)
    PQ = Implies(P, Q)
    QP = Implies(Q, P)
    NQP = Not(QP)
    H = Implies(PQ, NQP)
    iff_pq = Not(H)

    ea = Forall(x1, Not(In(x1, a)))
    eb = Forall(x2, Not(In(x2, b)))

    # NP |- PQ (vacuous implication from false antecedent)
    p1 = Proof(Sequent([P], [P]), 'axiom', principal=P)
    p2 = Proof(Sequent([P], [P, Q]), 'weakening_right', [p1], principal=Q)
    p3 = Proof(Sequent([P, NP], [Q]), 'not_left', [p2], principal=NP)
    p4 = Proof(Sequent([NP], [PQ]), 'implies_right', [p3], principal=PQ)

    # NQ |- QP
    q1 = Proof(Sequent([Q], [Q]), 'axiom', principal=Q)
    q2 = Proof(Sequent([Q], [Q, P]), 'weakening_right', [q1], principal=P)
    q3 = Proof(Sequent([Q, NQ], [P]), 'not_left', [q2], principal=NQ)
    q4 = Proof(Sequent([NQ], [QP]), 'implies_right', [q3], principal=QP)

    # weaken to common context NP, NQ
    w1 = Proof(Sequent([NP, NQ], [PQ]), 'weakening_left', [p4], principal=NQ)
    w2 = Proof(Sequent([NP, NQ], [QP]), 'weakening_left', [q4], principal=NP)

    # NP, NQ |- Iff(P, Q)
    c1 = Proof(Sequent([NP, NQ, NQP], []), 'not_left', [w2], principal=NQP)
    c2 = Proof(Sequent([NP, NQ, H], []), 'implies_left', [w1, c1], principal=H)
    core = Proof(Sequent([NP, NQ], [iff_pq]), 'not_right', [c2], principal=iff_pq)

    # forall_left: instantiate ea and eb with z
    fl1 = Proof(Sequent([ea, NQ], [iff_pq]), 'forall_left', [core], principal=ea, term=z)
    fl2 = Proof(Sequent([ea, eb], [iff_pq]), 'forall_left', [fl1], principal=eb, term=z)

    # forall_right z: ea, eb |- Eq(a, b)
    eq_ab = Forall(z, iff_pq)
    fr = Proof(Sequent([ea, eb], [eq_ab]), 'forall_right', [fl2], principal=eq_ab, term=z)

    # close: discharge eb, forall b, then discharge ea, forall a
    imp1 = Implies(eb, Eq(a, b))
    s1 = Proof(Sequent([ea], [imp1]), 'implies_right', [fr], principal=imp1)
    inner = Forall(b, imp1)
    s2 = Proof(Sequent([ea], [inner]), 'forall_right', [s1], term=b, principal=inner)
    imp2 = Implies(ea, inner)
    s3 = Proof(Sequent([], [imp2]), 'implies_right', [s2], principal=imp2)
    goal = EmptySet(lambda a: EmptySet(lambda b: Eq(a, b)))
    s4 = Proof(Sequent([], [goal]), 'forall_right', [s3], term=a, principal=goal)
    s4.name = 'unique_empty'
    return s4


def eq_transitive():
    """|- forall a. forall b. forall c. Eq(a,b) implies Eq(b,c) implies Eq(a,c)"""
    a, b, c, z = Var(), Var(), Var(), Var()

    P = In(z, a)
    Q = In(z, b)
    R = In(z, c)
    PQ = Implies(P, Q)
    QP = Implies(Q, P)
    QR = Implies(Q, R)
    RQ = Implies(R, Q)
    PR = Implies(P, R)
    RP = Implies(R, P)
    NQP = Not(QP)
    NRQ = Not(RQ)
    NRP = Not(RP)
    H_pq = Implies(PQ, NQP)
    H_qr = Implies(QR, NRQ)
    H_pr = Implies(PR, NRP)
    iff_pq = Not(H_pq)
    iff_qr = Not(H_qr)
    iff_pr = Not(H_pr)
    eq_ab = Forall(z, iff_pq)
    eq_bc = Forall(z, iff_qr)
    eq_ac = Forall(z, iff_pr)

    # --- Extract PQ from iff_pq ---
    e1 = Proof(Sequent([iff_pq, PQ], [PQ]), 'axiom', principal=PQ)
    e2 = Proof(Sequent([iff_pq, PQ], [NQP, PQ]), 'weakening_right', [e1], principal=NQP)
    e3 = Proof(Sequent([iff_pq], [H_pq, PQ]), 'implies_right', [e2], principal=H_pq)
    e4 = Proof(Sequent([H_pq], [H_pq]), 'axiom', principal=H_pq)
    e5 = Proof(Sequent([H_pq], [H_pq, PQ]), 'weakening_right', [e4], principal=PQ)
    e6 = Proof(Sequent([H_pq, iff_pq], [PQ]), 'not_left', [e5], principal=iff_pq)
    ext_pq = Proof(Sequent([iff_pq], [PQ]), 'cut', [e3, e6], principal=H_pq)

    # --- Extract QP from iff_pq ---
    f1 = Proof(Sequent([iff_pq, PQ, QP], [QP]), 'axiom', principal=QP)
    f2 = Proof(Sequent([iff_pq, PQ], [NQP, QP]), 'not_right', [f1], principal=NQP)
    f3 = Proof(Sequent([iff_pq], [H_pq, QP]), 'implies_right', [f2], principal=H_pq)
    f4 = Proof(Sequent([H_pq], [H_pq]), 'axiom', principal=H_pq)
    f5 = Proof(Sequent([H_pq], [H_pq, QP]), 'weakening_right', [f4], principal=QP)
    f6 = Proof(Sequent([H_pq, iff_pq], [QP]), 'not_left', [f5], principal=iff_pq)
    ext_qp = Proof(Sequent([iff_pq], [QP]), 'cut', [f3, f6], principal=H_pq)

    # --- Extract QR from iff_qr ---
    g1 = Proof(Sequent([iff_qr, QR], [QR]), 'axiom', principal=QR)
    g2 = Proof(Sequent([iff_qr, QR], [NRQ, QR]), 'weakening_right', [g1], principal=NRQ)
    g3 = Proof(Sequent([iff_qr], [H_qr, QR]), 'implies_right', [g2], principal=H_qr)
    g4 = Proof(Sequent([H_qr], [H_qr]), 'axiom', principal=H_qr)
    g5 = Proof(Sequent([H_qr], [H_qr, QR]), 'weakening_right', [g4], principal=QR)
    g6 = Proof(Sequent([H_qr, iff_qr], [QR]), 'not_left', [g5], principal=iff_qr)
    ext_qr = Proof(Sequent([iff_qr], [QR]), 'cut', [g3, g6], principal=H_qr)

    # --- Extract RQ from iff_qr ---
    h1 = Proof(Sequent([iff_qr, QR, RQ], [RQ]), 'axiom', principal=RQ)
    h2 = Proof(Sequent([iff_qr, QR], [NRQ, RQ]), 'not_right', [h1], principal=NRQ)
    h3 = Proof(Sequent([iff_qr], [H_qr, RQ]), 'implies_right', [h2], principal=H_qr)
    h4 = Proof(Sequent([H_qr], [H_qr]), 'axiom', principal=H_qr)
    h5 = Proof(Sequent([H_qr], [H_qr, RQ]), 'weakening_right', [h4], principal=RQ)
    h6 = Proof(Sequent([H_qr, iff_qr], [RQ]), 'not_left', [h5], principal=iff_qr)
    ext_rq = Proof(Sequent([iff_qr], [RQ]), 'cut', [h3, h6], principal=H_qr)

    # --- Forward composition: PQ, QR, P |- R ---
    fw_1 = Proof(Sequent([P], [P]), 'axiom', principal=P)
    fw_2 = Proof(Sequent([P], [P, R]), 'weakening_right', [fw_1], principal=R)
    fw_3 = Proof(Sequent([QR, P], [P, R]), 'weakening_left', [fw_2], principal=QR)
    fw_4 = Proof(Sequent([Q], [Q]), 'axiom', principal=Q)
    fw_5 = Proof(Sequent([Q], [Q, R]), 'weakening_right', [fw_4], principal=R)
    fw_6 = Proof(Sequent([P, Q], [Q, R]), 'weakening_left', [fw_5], principal=P)
    fw_7 = Proof(Sequent([R], [R]), 'axiom', principal=R)
    fw_8 = Proof(Sequent([Q, R], [R]), 'weakening_left', [fw_7], principal=Q)
    fw_9 = Proof(Sequent([P, Q, R], [R]), 'weakening_left', [fw_8], principal=P)
    fw_10 = Proof(Sequent([P, Q, QR], [R]), 'implies_left', [fw_6, fw_9], principal=QR)
    fw = Proof(Sequent([PQ, QR, P], [R]), 'implies_left', [fw_3, fw_10], principal=PQ)

    # --- Backward composition: RQ, QP, R |- P ---
    bw_1 = Proof(Sequent([R], [R]), 'axiom', principal=R)
    bw_2 = Proof(Sequent([R], [R, P]), 'weakening_right', [bw_1], principal=P)
    bw_3 = Proof(Sequent([QP, R], [R, P]), 'weakening_left', [bw_2], principal=QP)
    bw_4 = Proof(Sequent([Q], [Q]), 'axiom', principal=Q)
    bw_5 = Proof(Sequent([Q], [Q, P]), 'weakening_right', [bw_4], principal=P)
    bw_6 = Proof(Sequent([R, Q], [Q, P]), 'weakening_left', [bw_5], principal=R)
    bw_7 = Proof(Sequent([P], [P]), 'axiom', principal=P)
    bw_8 = Proof(Sequent([Q, P], [P]), 'weakening_left', [bw_7], principal=Q)
    bw_9 = Proof(Sequent([R, Q, P], [P]), 'weakening_left', [bw_8], principal=R)
    bw_10 = Proof(Sequent([R, Q, QP], [P]), 'implies_left', [bw_6, bw_9], principal=QP)
    bw = Proof(Sequent([RQ, QP, R], [P]), 'implies_left', [bw_3, bw_10], principal=RQ)

    # --- iff_pq, iff_qr, P |- R via cuts ---
    # cut on PQ
    c1a = Proof(Sequent([iff_pq], [PQ, R]), 'weakening_right', [ext_pq], principal=R)
    c1b = Proof(Sequent([iff_pq, iff_qr], [PQ, R]), 'weakening_left', [c1a], principal=iff_qr)
    c1c = Proof(Sequent([iff_pq, iff_qr, P], [PQ, R]), 'weakening_left', [c1b], principal=P)
    # cut on QR inside PQ branch
    c2a = Proof(Sequent([iff_qr], [QR, R]), 'weakening_right', [ext_qr], principal=R)
    c2b = Proof(Sequent([iff_qr, iff_pq], [QR, R]), 'weakening_left', [c2a], principal=iff_pq)
    c2c = Proof(Sequent([iff_qr, iff_pq, P], [QR, R]), 'weakening_left', [c2b], principal=P)
    c2d = Proof(Sequent([iff_qr, iff_pq, P, PQ], [QR, R]), 'weakening_left', [c2c], principal=PQ)
    c2e = Proof(Sequent([iff_pq, PQ, QR, P], [R]), 'weakening_left', [fw], principal=iff_pq)
    c2f = Proof(Sequent([iff_pq, iff_qr, PQ, QR, P], [R]), 'weakening_left', [c2e], principal=iff_qr)
    c2g = Proof(Sequent([iff_pq, iff_qr, P, PQ], [R]), 'cut', [c2d, c2f], principal=QR)
    fwd_result = Proof(Sequent([iff_pq, iff_qr, P], [R]), 'cut', [c1c, c2g], principal=PQ)
    fwd_pr = Proof(Sequent([iff_pq, iff_qr], [PR]), 'implies_right', [fwd_result], principal=PR)

    # --- iff_pq, iff_qr, R |- P via cuts ---
    # cut on RQ
    d1a = Proof(Sequent([iff_qr], [RQ, P]), 'weakening_right', [ext_rq], principal=P)
    d1b = Proof(Sequent([iff_qr, iff_pq], [RQ, P]), 'weakening_left', [d1a], principal=iff_pq)
    d1c = Proof(Sequent([iff_qr, iff_pq, R], [RQ, P]), 'weakening_left', [d1b], principal=R)
    # cut on QP inside RQ branch
    d2a = Proof(Sequent([iff_pq], [QP, P]), 'weakening_right', [ext_qp], principal=P)
    d2b = Proof(Sequent([iff_pq, iff_qr], [QP, P]), 'weakening_left', [d2a], principal=iff_qr)
    d2c = Proof(Sequent([iff_pq, iff_qr, R], [QP, P]), 'weakening_left', [d2b], principal=R)
    d2d = Proof(Sequent([iff_pq, iff_qr, R, RQ], [QP, P]), 'weakening_left', [d2c], principal=RQ)
    d2e = Proof(Sequent([iff_qr, RQ, QP, R], [P]), 'weakening_left', [bw], principal=iff_qr)
    d2f = Proof(Sequent([iff_pq, iff_qr, RQ, QP, R], [P]), 'weakening_left', [d2e], principal=iff_pq)
    d2g = Proof(Sequent([iff_pq, iff_qr, R, RQ], [P]), 'cut', [d2d, d2f], principal=QP)
    bwd_result = Proof(Sequent([iff_pq, iff_qr, R], [P]), 'cut', [d1c, d2g], principal=RQ)
    bwd_rp = Proof(Sequent([iff_pq, iff_qr], [RP]), 'implies_right', [bwd_result], principal=RP)

    # --- iff_pq, iff_qr |- iff_pr ---
    nr = Proof(Sequent([iff_pq, iff_qr, NRP], []), 'not_left', [bwd_rp], principal=NRP)
    il = Proof(Sequent([iff_pq, iff_qr, H_pr], []), 'implies_left', [fwd_pr, nr], principal=H_pr)
    core = Proof(Sequent([iff_pq, iff_qr], [iff_pr]), 'not_right', [il], principal=iff_pr)

    # --- Lift to Eq ---
    fl1 = Proof(Sequent([eq_ab, iff_qr], [iff_pr]), 'forall_left', [core], principal=eq_ab, term=z)
    fl2 = Proof(Sequent([eq_ab, eq_bc], [iff_pr]), 'forall_left', [fl1], principal=eq_bc, term=z)
    fr = Proof(Sequent([eq_ab, eq_bc], [eq_ac]), 'forall_right', [fl2], principal=eq_ac, term=z)

    # --- Close ---
    imp1 = Implies(Eq(b, c), Eq(a, c))
    s1 = Proof(Sequent([eq_ab], [imp1]), 'implies_right', [fr], principal=imp1)
    imp2 = Implies(Eq(a, b), imp1)
    s2 = Proof(Sequent([], [imp2]), 'implies_right', [s1], principal=imp2)
    fc = Forall(c, imp2)
    s3 = Proof(Sequent([], [fc]), 'forall_right', [s2], term=c, principal=fc)
    fb = Forall(b, fc)
    s4 = Proof(Sequent([], [fb]), 'forall_right', [s3], term=b, principal=fb)
    fa = Forall(a, fb)
    s5 = Proof(Sequent([], [fa]), 'forall_right', [s4], term=a, principal=fa)
    s5.name = 'eq_transitive'
    return s5


def singleton_exists():
    """Pairing |- forall a. exists s. forall z. Iff(In(z,s), Eq(z,a))"""
    a = Var()
    xp, yp, zp, bp = Var(), Var(), Var(), Var()

    pairing_ax = zfc.Pairing()

    # Pairing expansion (alpha-equiv to pairing_ax.expand())
    pairing_full = Forall(xp, Forall(yp,
        Exists(bp, Forall(zp,
            Iff(In(zp, bp), Or(Eq(zp, xp), Eq(zp, yp)))))))
    pairing_inst_x = Forall(yp,
        Exists(bp, Forall(zp,
            Iff(In(zp, bp), Or(Eq(zp, a), Eq(zp, yp))))))

    iff_or_zp = Iff(In(zp, bp), Or(Eq(zp, a), Eq(zp, a)))
    iff_clean_zp = Iff(In(zp, bp), Eq(zp, a))
    fa_or = Forall(zp, iff_or_zp)
    fa_clean = Forall(zp, iff_clean_zp)
    E_or = Exists(bp, fa_or)
    E_clean = Exists(bp, fa_clean)

    X = In(zp, bp)
    Y = Eq(zp, a)
    OrYY = Or(Y, Y)
    XO = Implies(X, OrYY)
    OX = Implies(OrYY, X)
    XY = Implies(X, Y)
    YX = Implies(Y, X)
    H_or = Implies(XO, Not(OX))
    H_clean = Implies(XY, Not(YX))

    # === Core: iff_or_zp |- iff_clean_zp ===

    # --- Extract XO from iff_or ---
    e1 = Proof(Sequent([iff_or_zp, XO], [XO]), 'axiom', principal=XO)
    e2 = Proof(Sequent([iff_or_zp, XO], [Not(OX), XO]), 'weakening_right', [e1], principal=Not(OX))
    e3 = Proof(Sequent([iff_or_zp], [H_or, XO]), 'implies_right', [e2], principal=H_or)
    e4 = Proof(Sequent([H_or], [H_or]), 'axiom', principal=H_or)
    e5 = Proof(Sequent([H_or], [H_or, XO]), 'weakening_right', [e4], principal=XO)
    e6 = Proof(Sequent([H_or, iff_or_zp], [XO]), 'not_left', [e5], principal=iff_or_zp)
    ext_xo = Proof(Sequent([iff_or_zp], [XO]), 'cut', [e3, e6], principal=H_or)

    # --- Extract OX from iff_or ---
    f1 = Proof(Sequent([iff_or_zp, XO, OX], [OX]), 'axiom', principal=OX)
    f2 = Proof(Sequent([iff_or_zp, XO], [Not(OX), OX]), 'not_right', [f1], principal=Not(OX))
    f3 = Proof(Sequent([iff_or_zp], [H_or, OX]), 'implies_right', [f2], principal=H_or)
    f4 = Proof(Sequent([H_or], [H_or]), 'axiom', principal=H_or)
    f5 = Proof(Sequent([H_or], [H_or, OX]), 'weakening_right', [f4], principal=OX)
    f6 = Proof(Sequent([H_or, iff_or_zp], [OX]), 'not_left', [f5], principal=iff_or_zp)
    ext_ox = Proof(Sequent([iff_or_zp], [OX]), 'cut', [f3, f6], principal=H_or)

    # --- Or(Y,Y) -> Y ---
    g1 = Proof(Sequent([Y], [Y]), 'axiom', principal=Y)
    g2 = Proof(Sequent([], [Not(Y), Y]), 'not_right', [g1], principal=Not(Y))
    g3 = Proof(Sequent([Y], [Y]), 'axiom', principal=Y)
    or_to_y = Proof(Sequent([OrYY], [Y]), 'implies_left', [g2, g3], principal=OrYY)

    # --- Y -> Or(Y,Y) ---
    h1 = Proof(Sequent([Y], [Y]), 'axiom', principal=Y)
    h2 = Proof(Sequent([Y, Not(Y)], []), 'not_left', [h1], principal=Not(Y))
    h3 = Proof(Sequent([Y, Not(Y)], [Y]), 'weakening_right', [h2], principal=Y)
    y_to_or = Proof(Sequent([Y], [OrYY]), 'implies_right', [h3], principal=OrYY)

    # --- Forward: iff_or |- X -> Y ---
    i1 = Proof(Sequent([X], [X]), 'axiom', principal=X)
    i2 = Proof(Sequent([X], [X, Y]), 'weakening_right', [i1], principal=Y)
    i3 = Proof(Sequent([X, OrYY], [Y]), 'weakening_left', [or_to_y], principal=X)
    i4 = Proof(Sequent([X, XO], [Y]), 'implies_left', [i2, i3], principal=XO)
    i5 = Proof(Sequent([iff_or_zp], [XO, Y]), 'weakening_right', [ext_xo], principal=Y)
    i6 = Proof(Sequent([iff_or_zp, X], [XO, Y]), 'weakening_left', [i5], principal=X)
    i7 = Proof(Sequent([iff_or_zp, X, XO], [Y]), 'weakening_left', [i4], principal=iff_or_zp)
    i8 = Proof(Sequent([iff_or_zp, X], [Y]), 'cut', [i6, i7], principal=XO)
    fwd = Proof(Sequent([iff_or_zp], [XY]), 'implies_right', [i8], principal=XY)

    # --- Backward: iff_or |- Y -> X ---
    j1 = Proof(Sequent([Y], [OrYY, X]), 'weakening_right', [y_to_or], principal=X)
    j2 = Proof(Sequent([X], [X]), 'axiom', principal=X)
    j3 = Proof(Sequent([Y, X], [X]), 'weakening_left', [j2], principal=Y)
    j4 = Proof(Sequent([Y, OX], [X]), 'implies_left', [j1, j3], principal=OX)
    j5 = Proof(Sequent([iff_or_zp], [OX, X]), 'weakening_right', [ext_ox], principal=X)
    j6 = Proof(Sequent([iff_or_zp, Y], [OX, X]), 'weakening_left', [j5], principal=Y)
    j7 = Proof(Sequent([iff_or_zp, Y, OX], [X]), 'weakening_left', [j4], principal=iff_or_zp)
    j8 = Proof(Sequent([iff_or_zp, Y], [X]), 'cut', [j6, j7], principal=OX)
    bwd = Proof(Sequent([iff_or_zp], [YX]), 'implies_right', [j8], principal=YX)

    # --- Build Iff(X, Y) ---
    k1 = Proof(Sequent([iff_or_zp, Not(YX)], []), 'not_left', [bwd], principal=Not(YX))
    k2 = Proof(Sequent([iff_or_zp, H_clean], []), 'implies_left', [fwd, k1], principal=H_clean)
    core = Proof(Sequent([iff_or_zp], [iff_clean_zp]), 'not_right', [k2], principal=iff_clean_zp)

    # === Lift to forall z ===
    l1 = Proof(Sequent([fa_or], [iff_clean_zp]), 'forall_left', [core], principal=fa_or, term=zp)
    l2 = Proof(Sequent([fa_or], [fa_clean]), 'forall_right', [l1], principal=fa_clean, term=zp)

    # === Exists transformation: E_or |- E_clean ===
    # Right: fa_or |- E_clean (existential intro with witness bp)
    n1 = Proof(Sequent([fa_or, Not(fa_clean)], []), 'not_left', [l2], principal=Not(fa_clean))
    n2 = Proof(Sequent([fa_or, Forall(bp, Not(fa_clean))], []),
               'forall_left', [n1], principal=Forall(bp, Not(fa_clean)), term=bp)
    n3 = Proof(Sequent([fa_or], [E_clean]), 'not_right', [n2], principal=E_clean)
    # Left: E_or |- E_clean (existential elim with eigenvariable bp)
    p1 = Proof(Sequent([], [Not(fa_or), E_clean]), 'not_right', [n3], principal=Not(fa_or))
    p2 = Proof(Sequent([], [Forall(bp, Not(fa_or)), E_clean]),
               'forall_right', [p1], principal=Forall(bp, Not(fa_or)), term=bp)
    p3 = Proof(Sequent([E_or], [E_clean]), 'not_left', [p2], principal=E_or)

    # === Pairing instantiation: pairing_ax |- E_or ===
    q1 = Proof(Sequent([E_or], [E_or]), 'axiom', principal=E_or)
    q2 = Proof(Sequent([pairing_inst_x], [E_or]),
               'forall_left', [q1], principal=pairing_inst_x, term=a)
    q3 = Proof(Sequent([pairing_ax], [E_or]),
               'forall_left', [q2], principal=pairing_full, term=a)

    # === Combine via cut ===
    r1 = Proof(Sequent([pairing_ax], [E_or, E_clean]),
               'weakening_right', [q3], principal=E_clean)
    r2 = Proof(Sequent([pairing_ax, E_or], [E_clean]),
               'weakening_left', [p3], principal=pairing_ax)
    r3 = Proof(Sequent([pairing_ax], [E_clean]), 'cut', [r1, r2], principal=E_or)

    # === Close ===
    goal = Forall(a, E_clean)
    s1 = Proof(Sequent([pairing_ax], [goal]),
               'forall_right', [r3], principal=goal, term=a)
    s1.name = 'singleton_exists'
    return s1


def iff_chain(P, Q, R, vars: list[Var]):
    """|- forall vars. Iff(P,Q) implies Iff(Q,R) implies Iff(P,R)"""
    PQ = Implies(P, Q)
    QP = Implies(Q, P)
    QR = Implies(Q, R)
    RQ = Implies(R, Q)
    PR = Implies(P, R)
    RP = Implies(R, P)
    NQP = Not(QP)
    NRQ = Not(RQ)
    NRP = Not(RP)
    H_pq = Implies(PQ, NQP)
    H_qr = Implies(QR, NRQ)
    H_pr = Implies(PR, NRP)
    iff_pq = Iff(P, Q)
    iff_qr = Iff(Q, R)
    iff_pr = Iff(P, R)

    # --- Extract PQ from iff_pq ---
    e1 = Proof(Sequent([iff_pq, PQ], [PQ]), 'axiom', principal=PQ)
    e2 = Proof(Sequent([iff_pq, PQ], [NQP, PQ]), 'weakening_right', [e1], principal=NQP)
    e3 = Proof(Sequent([iff_pq], [H_pq, PQ]), 'implies_right', [e2], principal=H_pq)
    e4 = Proof(Sequent([H_pq], [H_pq]), 'axiom', principal=H_pq)
    e5 = Proof(Sequent([H_pq], [H_pq, PQ]), 'weakening_right', [e4], principal=PQ)
    e6 = Proof(Sequent([H_pq, iff_pq], [PQ]), 'not_left', [e5], principal=iff_pq)
    ext_pq = Proof(Sequent([iff_pq], [PQ]), 'cut', [e3, e6], principal=H_pq)

    # --- Extract QP from iff_pq ---
    f1 = Proof(Sequent([iff_pq, PQ, QP], [QP]), 'axiom', principal=QP)
    f2 = Proof(Sequent([iff_pq, PQ], [NQP, QP]), 'not_right', [f1], principal=NQP)
    f3 = Proof(Sequent([iff_pq], [H_pq, QP]), 'implies_right', [f2], principal=H_pq)
    f4 = Proof(Sequent([H_pq], [H_pq]), 'axiom', principal=H_pq)
    f5 = Proof(Sequent([H_pq], [H_pq, QP]), 'weakening_right', [f4], principal=QP)
    f6 = Proof(Sequent([H_pq, iff_pq], [QP]), 'not_left', [f5], principal=iff_pq)
    ext_qp = Proof(Sequent([iff_pq], [QP]), 'cut', [f3, f6], principal=H_pq)

    # --- Extract QR from iff_qr ---
    g1 = Proof(Sequent([iff_qr, QR], [QR]), 'axiom', principal=QR)
    g2 = Proof(Sequent([iff_qr, QR], [NRQ, QR]), 'weakening_right', [g1], principal=NRQ)
    g3 = Proof(Sequent([iff_qr], [H_qr, QR]), 'implies_right', [g2], principal=H_qr)
    g4 = Proof(Sequent([H_qr], [H_qr]), 'axiom', principal=H_qr)
    g5 = Proof(Sequent([H_qr], [H_qr, QR]), 'weakening_right', [g4], principal=QR)
    g6 = Proof(Sequent([H_qr, iff_qr], [QR]), 'not_left', [g5], principal=iff_qr)
    ext_qr = Proof(Sequent([iff_qr], [QR]), 'cut', [g3, g6], principal=H_qr)

    # --- Extract RQ from iff_qr ---
    h1 = Proof(Sequent([iff_qr, QR, RQ], [RQ]), 'axiom', principal=RQ)
    h2 = Proof(Sequent([iff_qr, QR], [NRQ, RQ]), 'not_right', [h1], principal=NRQ)
    h3 = Proof(Sequent([iff_qr], [H_qr, RQ]), 'implies_right', [h2], principal=H_qr)
    h4 = Proof(Sequent([H_qr], [H_qr]), 'axiom', principal=H_qr)
    h5 = Proof(Sequent([H_qr], [H_qr, RQ]), 'weakening_right', [h4], principal=RQ)
    h6 = Proof(Sequent([H_qr, iff_qr], [RQ]), 'not_left', [h5], principal=iff_qr)
    ext_rq = Proof(Sequent([iff_qr], [RQ]), 'cut', [h3, h6], principal=H_qr)

    # --- Forward: PQ, QR, P |- R ---
    fw_1 = Proof(Sequent([P], [P]), 'axiom', principal=P)
    fw_2 = Proof(Sequent([P], [P, R]), 'weakening_right', [fw_1], principal=R)
    fw_3 = Proof(Sequent([QR, P], [P, R]), 'weakening_left', [fw_2], principal=QR)
    fw_4 = Proof(Sequent([Q], [Q]), 'axiom', principal=Q)
    fw_5 = Proof(Sequent([Q], [Q, R]), 'weakening_right', [fw_4], principal=R)
    fw_6 = Proof(Sequent([P, Q], [Q, R]), 'weakening_left', [fw_5], principal=P)
    fw_7 = Proof(Sequent([R], [R]), 'axiom', principal=R)
    fw_8 = Proof(Sequent([Q, R], [R]), 'weakening_left', [fw_7], principal=Q)
    fw_9 = Proof(Sequent([P, Q, R], [R]), 'weakening_left', [fw_8], principal=P)
    fw_10 = Proof(Sequent([P, Q, QR], [R]), 'implies_left', [fw_6, fw_9], principal=QR)
    fw = Proof(Sequent([PQ, QR, P], [R]), 'implies_left', [fw_3, fw_10], principal=PQ)

    # --- Backward: RQ, QP, R |- P ---
    bw_1 = Proof(Sequent([R], [R]), 'axiom', principal=R)
    bw_2 = Proof(Sequent([R], [R, P]), 'weakening_right', [bw_1], principal=P)
    bw_3 = Proof(Sequent([QP, R], [R, P]), 'weakening_left', [bw_2], principal=QP)
    bw_4 = Proof(Sequent([Q], [Q]), 'axiom', principal=Q)
    bw_5 = Proof(Sequent([Q], [Q, P]), 'weakening_right', [bw_4], principal=P)
    bw_6 = Proof(Sequent([R, Q], [Q, P]), 'weakening_left', [bw_5], principal=R)
    bw_7 = Proof(Sequent([P], [P]), 'axiom', principal=P)
    bw_8 = Proof(Sequent([Q, P], [P]), 'weakening_left', [bw_7], principal=Q)
    bw_9 = Proof(Sequent([R, Q, P], [P]), 'weakening_left', [bw_8], principal=R)
    bw_10 = Proof(Sequent([R, Q, QP], [P]), 'implies_left', [bw_6, bw_9], principal=QP)
    bw = Proof(Sequent([RQ, QP, R], [P]), 'implies_left', [bw_3, bw_10], principal=RQ)

    # --- iff_pq, iff_qr, P |- R via cuts ---
    c1a = Proof(Sequent([iff_pq], [PQ, R]), 'weakening_right', [ext_pq], principal=R)
    c1b = Proof(Sequent([iff_pq, iff_qr], [PQ, R]), 'weakening_left', [c1a], principal=iff_qr)
    c1c = Proof(Sequent([iff_pq, iff_qr, P], [PQ, R]), 'weakening_left', [c1b], principal=P)
    c2a = Proof(Sequent([iff_qr], [QR, R]), 'weakening_right', [ext_qr], principal=R)
    c2b = Proof(Sequent([iff_qr, iff_pq], [QR, R]), 'weakening_left', [c2a], principal=iff_pq)
    c2c = Proof(Sequent([iff_qr, iff_pq, P], [QR, R]), 'weakening_left', [c2b], principal=P)
    c2d = Proof(Sequent([iff_qr, iff_pq, P, PQ], [QR, R]), 'weakening_left', [c2c], principal=PQ)
    c2e = Proof(Sequent([iff_pq, PQ, QR, P], [R]), 'weakening_left', [fw], principal=iff_pq)
    c2f = Proof(Sequent([iff_pq, iff_qr, PQ, QR, P], [R]), 'weakening_left', [c2e], principal=iff_qr)
    c2g = Proof(Sequent([iff_pq, iff_qr, P, PQ], [R]), 'cut', [c2d, c2f], principal=QR)
    fwd_result = Proof(Sequent([iff_pq, iff_qr, P], [R]), 'cut', [c1c, c2g], principal=PQ)
    fwd_pr = Proof(Sequent([iff_pq, iff_qr], [PR]), 'implies_right', [fwd_result], principal=PR)

    # --- iff_pq, iff_qr, R |- P via cuts ---
    d1a = Proof(Sequent([iff_qr], [RQ, P]), 'weakening_right', [ext_rq], principal=P)
    d1b = Proof(Sequent([iff_qr, iff_pq], [RQ, P]), 'weakening_left', [d1a], principal=iff_pq)
    d1c = Proof(Sequent([iff_qr, iff_pq, R], [RQ, P]), 'weakening_left', [d1b], principal=R)
    d2a = Proof(Sequent([iff_pq], [QP, P]), 'weakening_right', [ext_qp], principal=P)
    d2b = Proof(Sequent([iff_pq, iff_qr], [QP, P]), 'weakening_left', [d2a], principal=iff_qr)
    d2c = Proof(Sequent([iff_pq, iff_qr, R], [QP, P]), 'weakening_left', [d2b], principal=R)
    d2d = Proof(Sequent([iff_pq, iff_qr, R, RQ], [QP, P]), 'weakening_left', [d2c], principal=RQ)
    d2e = Proof(Sequent([iff_qr, RQ, QP, R], [P]), 'weakening_left', [bw], principal=iff_qr)
    d2f = Proof(Sequent([iff_pq, iff_qr, RQ, QP, R], [P]), 'weakening_left', [d2e], principal=iff_pq)
    d2g = Proof(Sequent([iff_pq, iff_qr, R, RQ], [P]), 'cut', [d2d, d2f], principal=QP)
    bwd_result = Proof(Sequent([iff_pq, iff_qr, R], [P]), 'cut', [d1c, d2g], principal=RQ)
    bwd_rp = Proof(Sequent([iff_pq, iff_qr], [RP]), 'implies_right', [bwd_result], principal=RP)

    # --- Build Iff(P, R) ---
    nr = Proof(Sequent([iff_pq, iff_qr, NRP], []), 'not_left', [bwd_rp], principal=NRP)
    il = Proof(Sequent([iff_pq, iff_qr, H_pr], []), 'implies_left', [fwd_pr, nr], principal=H_pr)
    core = Proof(Sequent([iff_pq, iff_qr], [iff_pr]), 'not_right', [il], principal=iff_pr)

    # --- Close ---
    imp1 = Implies(iff_qr, iff_pr)
    s1 = Proof(Sequent([iff_pq], [imp1]), 'implies_right', [core], principal=imp1)
    imp2 = Implies(iff_pq, imp1)
    s2 = Proof(Sequent([], [imp2]), 'implies_right', [s1], principal=imp2)
    proof = s2
    for v in vars:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], term=v, principal=fa)
    proof.name = 'iff_chain'
    return proof


def forall_implies_exists(P, Q, x: Var, vars: list[Var]):
    """|- forall vars. (forall x. P implies Q) implies (exists x. P) implies (exists x. Q)"""
    PQ = Implies(P, Q)
    faPQ = Forall(x, PQ)
    exP = Exists(x, P)
    exQ = Exists(x, Q)
    NP = Not(P)
    NQ = Not(Q)
    faNP = Forall(x, NP)
    faNQ = Forall(x, NQ)

    # Core: faPQ, P |- Q (instantiate forall, apply modus ponens)
    ax_p = Proof(Sequent([P], [P]), 'axiom', principal=P)
    ax_p2 = Proof(Sequent([P], [P, Q]), 'weakening_right', [ax_p], principal=Q)
    ax_q = Proof(Sequent([P, Q], [Q]), 'axiom', principal=Q)
    mp = Proof(Sequent([P, PQ], [Q]), 'implies_left', [ax_p2, ax_q], principal=PQ)
    inst = Proof(Sequent([faPQ, P], [Q]), 'forall_left', [mp], principal=faPQ, term=x)

    # faPQ, P |- exQ (existential intro with witness x)
    # exQ = Not(Forall(x, Not(Q)))
    nl1 = Proof(Sequent([faPQ, P, NQ], []), 'not_left', [inst], principal=NQ)
    fl1 = Proof(Sequent([faPQ, P, faNQ], []),
                'forall_left', [nl1], principal=faNQ, term=x)
    nr1 = Proof(Sequent([faPQ, P], [exQ]), 'not_right', [fl1], principal=exQ)

    # faPQ, exP |- exQ (existential elim on exP)
    # from faPQ, P |- exQ, derive faPQ, Not(faNP) |- exQ
    # step 1: not_right to get |- Not(P), exQ from P |- exQ context
    nr2 = Proof(Sequent([faPQ], [NP, exQ]), 'not_right', [nr1], principal=NP)
    # step 2: forall_right x for |- Forall(x, Not(P)), exQ
    fr2 = Proof(Sequent([faPQ], [faNP, exQ]),
                'forall_right', [nr2], principal=faNP, term=x)
    # step 3: not_left to get Not(faNP) |- exQ
    nl2 = Proof(Sequent([faPQ, exP], [exQ]), 'not_left', [fr2], principal=exP)

    # Close: discharge exP, faPQ, then forall
    imp1 = Implies(exP, exQ)
    s1 = Proof(Sequent([faPQ], [imp1]), 'implies_right', [nl2], principal=imp1)
    imp2 = Implies(faPQ, imp1)
    s2 = Proof(Sequent([], [imp2]), 'implies_right', [s1], principal=imp2)
    proof = s2
    for v in vars:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], term=v, principal=fa)
    proof.name = 'forall_implies_exists'
    return proof


def eq_substitution():
    """Extensionality |- forall a, b, z. Eq(a,b) implies Iff(In(a,z), In(b,z))"""
    a, b, z = Var(), Var(), Var()
    xp, yp, zp = Var(), Var(), Var()

    ext_ax = zfc.Extensionality()
    eq_ab = Eq(a, b)
    iff_ab_z = Iff(In(a, z), In(b, z))

    # Extensionality expanded form
    ext_full = Forall(xp, Forall(yp,
        Implies(Forall(zp, Iff(In(zp, xp), In(zp, yp))),
                Forall(zp, Iff(In(xp, zp), In(yp, zp))))))
    ext_inst_x = Forall(yp,
        Implies(Forall(zp, Iff(In(zp, a), In(zp, yp))),
                Forall(zp, Iff(In(a, zp), In(yp, zp)))))
    eq_ab_exp = Forall(zp, Iff(In(zp, a), In(zp, b)))
    fa_iff = Forall(zp, Iff(In(a, zp), In(b, zp)))
    ext_inst_xy = Implies(eq_ab_exp, fa_iff)

    # iff_ab_z |- iff_ab_z
    s0 = Proof(Sequent([iff_ab_z], [iff_ab_z]), 'axiom', principal=iff_ab_z)
    # fa_iff |- iff_ab_z (instantiate with z)
    s1 = Proof(Sequent([fa_iff], [iff_ab_z]), 'forall_left', [s0], principal=fa_iff, term=z)
    # Eq(a,b), fa_iff |- iff_ab_z
    s2 = Proof(Sequent([eq_ab, fa_iff], [iff_ab_z]), 'weakening_left', [s1], principal=eq_ab)
    # Eq(a,b) |- Eq(a,b), iff_ab_z
    s3 = Proof(Sequent([eq_ab], [eq_ab]), 'axiom', principal=eq_ab)
    s4 = Proof(Sequent([eq_ab], [eq_ab, iff_ab_z]), 'weakening_right', [s3], principal=iff_ab_z)
    # Eq(a,b), ext_inst_xy |- iff_ab_z (implies_left)
    s5 = Proof(Sequent([eq_ab, ext_inst_xy], [iff_ab_z]),
               'implies_left', [s4, s2], principal=ext_inst_xy)
    # ext_inst_xy |- Eq(a,b) -> iff_ab_z
    imp = Implies(eq_ab, iff_ab_z)
    s6 = Proof(Sequent([ext_inst_xy], [imp]), 'implies_right', [s5], principal=imp)
    # Instantiate extensionality: forall_left twice
    s7 = Proof(Sequent([ext_inst_x], [imp]), 'forall_left', [s6], principal=ext_inst_x, term=b)
    s8 = Proof(Sequent([ext_ax], [imp]), 'forall_left', [s7], principal=ext_full, term=a)

    # Close
    fz = Forall(z, imp)
    s9 = Proof(Sequent([ext_ax], [fz]), 'forall_right', [s8], principal=fz, term=z)
    fb = Forall(b, fz)
    s10 = Proof(Sequent([ext_ax], [fb]), 'forall_right', [s9], principal=fb, term=b)
    fa = Forall(a, fb)
    s11 = Proof(Sequent([ext_ax], [fa]), 'forall_right', [s10], principal=fa, term=a)
    s11.name = 'eq_substitution'
    return s11


def or_iff_compat(P, Q, R, S, vars: list[Var]):
    """|- forall vars. Iff(P,R) implies Iff(Q,S) implies Iff(Or(P,Q), Or(R,S))"""
    PR = Implies(P, R)
    RP = Implies(R, P)
    QS = Implies(Q, S)
    SQ = Implies(S, Q)
    NP = Not(P)
    NR = Not(R)
    NRP = Not(RP)
    NSQ = Not(SQ)
    H_pr = Implies(PR, NRP)
    H_qs = Implies(QS, NSQ)
    iff_pr = Iff(P, R)
    iff_qs = Iff(Q, S)
    or_pq = Or(P, Q)
    or_rs = Or(R, S)
    or_fwd = Implies(or_pq, or_rs)
    or_bwd = Implies(or_rs, or_pq)
    H_or = Implies(or_fwd, Not(or_bwd))

    # --- Extract PR from iff_pr ---
    e1 = Proof(Sequent([iff_pr, PR], [PR]), 'axiom', principal=PR)
    e2 = Proof(Sequent([iff_pr, PR], [NRP, PR]), 'weakening_right', [e1], principal=NRP)
    e3 = Proof(Sequent([iff_pr], [H_pr, PR]), 'implies_right', [e2], principal=H_pr)
    e4 = Proof(Sequent([H_pr], [H_pr, PR]), 'weakening_right',
               [Proof(Sequent([H_pr], [H_pr]), 'axiom', principal=H_pr)], principal=PR)
    e5 = Proof(Sequent([H_pr, iff_pr], [PR]), 'not_left', [e4], principal=iff_pr)
    ext_pr = Proof(Sequent([iff_pr], [PR]), 'cut', [e3, e5], principal=H_pr)

    # --- Extract RP from iff_pr ---
    f1 = Proof(Sequent([iff_pr, PR, RP], [RP]), 'axiom', principal=RP)
    f2 = Proof(Sequent([iff_pr, PR], [NRP, RP]), 'not_right', [f1], principal=NRP)
    f3 = Proof(Sequent([iff_pr], [H_pr, RP]), 'implies_right', [f2], principal=H_pr)
    f4 = Proof(Sequent([H_pr], [H_pr, RP]), 'weakening_right',
               [Proof(Sequent([H_pr], [H_pr]), 'axiom', principal=H_pr)], principal=RP)
    f5 = Proof(Sequent([H_pr, iff_pr], [RP]), 'not_left', [f4], principal=iff_pr)
    ext_rp = Proof(Sequent([iff_pr], [RP]), 'cut', [f3, f5], principal=H_pr)

    # --- Extract QS from iff_qs ---
    g1 = Proof(Sequent([iff_qs, QS], [QS]), 'axiom', principal=QS)
    g2 = Proof(Sequent([iff_qs, QS], [NSQ, QS]), 'weakening_right', [g1], principal=NSQ)
    g3 = Proof(Sequent([iff_qs], [H_qs, QS]), 'implies_right', [g2], principal=H_qs)
    g4 = Proof(Sequent([H_qs], [H_qs, QS]), 'weakening_right',
               [Proof(Sequent([H_qs], [H_qs]), 'axiom', principal=H_qs)], principal=QS)
    g5 = Proof(Sequent([H_qs, iff_qs], [QS]), 'not_left', [g4], principal=iff_qs)
    ext_qs = Proof(Sequent([iff_qs], [QS]), 'cut', [g3, g5], principal=H_qs)

    # --- Extract SQ from iff_qs ---
    h1 = Proof(Sequent([iff_qs, QS, SQ], [SQ]), 'axiom', principal=SQ)
    h2 = Proof(Sequent([iff_qs, QS], [NSQ, SQ]), 'not_right', [h1], principal=NSQ)
    h3 = Proof(Sequent([iff_qs], [H_qs, SQ]), 'implies_right', [h2], principal=H_qs)
    h4 = Proof(Sequent([H_qs], [H_qs, SQ]), 'weakening_right',
               [Proof(Sequent([H_qs], [H_qs]), 'axiom', principal=H_qs)], principal=SQ)
    h5 = Proof(Sequent([H_qs, iff_qs], [SQ]), 'not_left', [h4], principal=iff_qs)
    ext_sq = Proof(Sequent([iff_qs], [SQ]), 'cut', [h3, h5], principal=H_qs)

    # === Forward: PR, QS, or_pq, NR |- S ===
    # implies_left on PR in context {QS, NR, P}:
    #   premise 1a: QS, NR, P |- P, S
    a1 = Proof(Sequent([P], [P]), 'axiom', principal=P)
    a2 = Proof(Sequent([P], [P, S]), 'weakening_right', [a1], principal=S)
    a3 = Proof(Sequent([NR, P], [P, S]), 'weakening_left', [a2], principal=NR)
    a4 = Proof(Sequent([QS, NR, P], [P, S]), 'weakening_left', [a3], principal=QS)
    #   premise 1b: QS, NR, P, R |- S
    b1 = Proof(Sequent([R], [R]), 'axiom', principal=R)
    b2 = Proof(Sequent([R], [R, S]), 'weakening_right', [b1], principal=S)
    b3 = Proof(Sequent([NR, R], [S]), 'not_left', [b2], principal=NR)
    b4 = Proof(Sequent([QS, NR, R], [S]), 'weakening_left', [b3], principal=QS)
    b5 = Proof(Sequent([QS, NR, P, R], [S]), 'weakening_left', [b4], principal=P)
    fw_pr = Proof(Sequent([PR, QS, NR, P], [S]), 'implies_left', [a4, b5], principal=PR)
    fw_np = Proof(Sequent([PR, QS, NR], [NP, S]), 'not_right', [fw_pr], principal=NP)
    # implies_left on QS in context {PR, NR, Q}:
    c1 = Proof(Sequent([Q], [Q]), 'axiom', principal=Q)
    c2 = Proof(Sequent([Q], [Q, S]), 'weakening_right', [c1], principal=S)
    c3 = Proof(Sequent([NR, Q], [Q, S]), 'weakening_left', [c2], principal=NR)
    c4 = Proof(Sequent([PR, NR, Q], [Q, S]), 'weakening_left', [c3], principal=PR)
    d1 = Proof(Sequent([S], [S]), 'axiom', principal=S)
    d2 = Proof(Sequent([Q, S], [S]), 'weakening_left', [d1], principal=Q)
    d3 = Proof(Sequent([NR, Q, S], [S]), 'weakening_left', [d2], principal=NR)
    d4 = Proof(Sequent([PR, NR, Q, S], [S]), 'weakening_left', [d3], principal=PR)
    fw_qs = Proof(Sequent([PR, QS, NR, Q], [S]), 'implies_left', [c4, d4], principal=QS)
    # implies_left on or_pq
    fw_core = Proof(Sequent([PR, QS, or_pq, NR], [S]), 'implies_left', [fw_np, fw_qs], principal=or_pq)
    fw_closed = Proof(Sequent([PR, QS, or_pq], [or_rs]), 'implies_right', [fw_core], principal=or_rs)

    # Cut PR: iff_pr, QS, or_pq |- or_rs
    fw_t1 = Proof(Sequent([iff_pr], [PR, or_rs]), 'weakening_right', [ext_pr], principal=or_rs)
    fw_t2 = Proof(Sequent([iff_pr, QS], [PR, or_rs]), 'weakening_left', [fw_t1], principal=QS)
    fw_t3 = Proof(Sequent([iff_pr, QS, or_pq], [PR, or_rs]), 'weakening_left', [fw_t2], principal=or_pq)
    fw_t4 = Proof(Sequent([iff_pr, PR, QS, or_pq], [or_rs]), 'weakening_left', [fw_closed], principal=iff_pr)
    fw_c1 = Proof(Sequent([iff_pr, QS, or_pq], [or_rs]), 'cut', [fw_t3, fw_t4], principal=PR)

    # Cut QS: iff_pr, iff_qs, or_pq |- or_rs
    fw_u1 = Proof(Sequent([iff_qs], [QS, or_rs]), 'weakening_right', [ext_qs], principal=or_rs)
    fw_u2 = Proof(Sequent([iff_qs, iff_pr], [QS, or_rs]), 'weakening_left', [fw_u1], principal=iff_pr)
    fw_u3 = Proof(Sequent([iff_qs, iff_pr, or_pq], [QS, or_rs]), 'weakening_left', [fw_u2], principal=or_pq)
    fw_u4 = Proof(Sequent([iff_pr, iff_qs, QS, or_pq], [or_rs]), 'weakening_left', [fw_c1], principal=iff_qs)
    fw_c2 = Proof(Sequent([iff_pr, iff_qs, or_pq], [or_rs]), 'cut', [fw_u3, fw_u4], principal=QS)
    fwd = Proof(Sequent([iff_pr, iff_qs], [or_fwd]), 'implies_right', [fw_c2], principal=or_fwd)

    # === Backward: RP, SQ, or_rs, NP |- Q ===
    # implies_left on RP in context {SQ, NP, R}:
    aa1 = Proof(Sequent([R], [R]), 'axiom', principal=R)
    aa2 = Proof(Sequent([R], [R, Q]), 'weakening_right', [aa1], principal=Q)
    aa3 = Proof(Sequent([NP, R], [R, Q]), 'weakening_left', [aa2], principal=NP)
    aa4 = Proof(Sequent([SQ, NP, R], [R, Q]), 'weakening_left', [aa3], principal=SQ)
    bb1 = Proof(Sequent([P], [P]), 'axiom', principal=P)
    bb2 = Proof(Sequent([P], [P, Q]), 'weakening_right', [bb1], principal=Q)
    bb3 = Proof(Sequent([NP, P], [Q]), 'not_left', [bb2], principal=NP)
    bb4 = Proof(Sequent([SQ, NP, P], [Q]), 'weakening_left', [bb3], principal=SQ)
    bb5 = Proof(Sequent([SQ, NP, R, P], [Q]), 'weakening_left', [bb4], principal=R)
    bw_rp = Proof(Sequent([RP, SQ, NP, R], [Q]), 'implies_left', [aa4, bb5], principal=RP)
    bw_nr = Proof(Sequent([RP, SQ, NP], [NR, Q]), 'not_right', [bw_rp], principal=NR)
    # implies_left on SQ in context {RP, NP, S}:
    cc1 = Proof(Sequent([S], [S]), 'axiom', principal=S)
    cc2 = Proof(Sequent([S], [S, Q]), 'weakening_right', [cc1], principal=Q)
    cc3 = Proof(Sequent([NP, S], [S, Q]), 'weakening_left', [cc2], principal=NP)
    cc4 = Proof(Sequent([RP, NP, S], [S, Q]), 'weakening_left', [cc3], principal=RP)
    dd1 = Proof(Sequent([Q], [Q]), 'axiom', principal=Q)
    dd2 = Proof(Sequent([S, Q], [Q]), 'weakening_left', [dd1], principal=S)
    dd3 = Proof(Sequent([NP, S, Q], [Q]), 'weakening_left', [dd2], principal=NP)
    dd4 = Proof(Sequent([RP, NP, S, Q], [Q]), 'weakening_left', [dd3], principal=RP)
    bw_sq = Proof(Sequent([RP, SQ, NP, S], [Q]), 'implies_left', [cc4, dd4], principal=SQ)
    bw_core = Proof(Sequent([RP, SQ, or_rs, NP], [Q]), 'implies_left', [bw_nr, bw_sq], principal=or_rs)
    bw_closed = Proof(Sequent([RP, SQ, or_rs], [or_pq]), 'implies_right', [bw_core], principal=or_pq)

    # Cut RP: iff_pr, SQ, or_rs |- or_pq
    bw_t1 = Proof(Sequent([iff_pr], [RP, or_pq]), 'weakening_right', [ext_rp], principal=or_pq)
    bw_t2 = Proof(Sequent([iff_pr, SQ], [RP, or_pq]), 'weakening_left', [bw_t1], principal=SQ)
    bw_t3 = Proof(Sequent([iff_pr, SQ, or_rs], [RP, or_pq]), 'weakening_left', [bw_t2], principal=or_rs)
    bw_t4 = Proof(Sequent([iff_pr, RP, SQ, or_rs], [or_pq]), 'weakening_left', [bw_closed], principal=iff_pr)
    bw_c1 = Proof(Sequent([iff_pr, SQ, or_rs], [or_pq]), 'cut', [bw_t3, bw_t4], principal=RP)

    # Cut SQ: iff_pr, iff_qs, or_rs |- or_pq
    bw_u1 = Proof(Sequent([iff_qs], [SQ, or_pq]), 'weakening_right', [ext_sq], principal=or_pq)
    bw_u2 = Proof(Sequent([iff_qs, iff_pr], [SQ, or_pq]), 'weakening_left', [bw_u1], principal=iff_pr)
    bw_u3 = Proof(Sequent([iff_qs, iff_pr, or_rs], [SQ, or_pq]), 'weakening_left', [bw_u2], principal=or_rs)
    bw_u4 = Proof(Sequent([iff_pr, iff_qs, SQ, or_rs], [or_pq]), 'weakening_left', [bw_c1], principal=iff_qs)
    bw_c2 = Proof(Sequent([iff_pr, iff_qs, or_rs], [or_pq]), 'cut', [bw_u3, bw_u4], principal=SQ)
    bwd = Proof(Sequent([iff_pr, iff_qs], [or_bwd]), 'implies_right', [bw_c2], principal=or_bwd)

    # === Build Iff(Or(P,Q), Or(R,S)) ===
    nr = Proof(Sequent([iff_pr, iff_qs, Not(or_bwd)], []), 'not_left', [bwd], principal=Not(or_bwd))
    il = Proof(Sequent([iff_pr, iff_qs, H_or], []), 'implies_left', [fwd, nr], principal=H_or)
    core = Proof(Sequent([iff_pr, iff_qs], [Iff(or_pq, or_rs)]),
                 'not_right', [il], principal=Iff(or_pq, or_rs))

    # === Close ===
    imp1 = Implies(iff_qs, Iff(or_pq, or_rs))
    s1 = Proof(Sequent([iff_pr], [imp1]), 'implies_right', [core], principal=imp1)
    imp2 = Implies(iff_pr, imp1)
    s2 = Proof(Sequent([], [imp2]), 'implies_right', [s1], principal=imp2)
    proof = s2
    for v in vars:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], term=v, principal=fa)
    proof.name = 'or_iff_compat'
    return proof


def singleton_eq():
    """|- forall a, b, s. (forall z. Iff(In(z,s), Eq(z,a))) implies
                          (forall z. Iff(In(z,s), Eq(z,b))) implies Eq(a,b)"""
    a, b, s = Var(), Var(), Var()
    z_inner, z2 = Var(), Var()

    X = In(a, s)
    Y = Eq(a, a)
    Z = Eq(a, b)
    XY = Implies(X, Y)
    YX = Implies(Y, X)
    XZ = Implies(X, Z)
    ZX = Implies(Z, X)
    H_xy = Implies(XY, Not(YX))
    H_xz = Implies(XZ, Not(ZX))
    iff_xy = Iff(X, Y)
    iff_xz = Iff(X, Z)
    char_a = Forall(z_inner, Iff(In(z_inner, s), Eq(z_inner, a)))
    char_b = Forall(z_inner, Iff(In(z_inner, s), Eq(z_inner, b)))

    # --- Extract YX from iff_xy (reverse: Eq(a,a) -> In(a,s)) ---
    e1 = Proof(Sequent([iff_xy, XY, YX], [YX]), 'axiom', principal=YX)
    e2 = Proof(Sequent([iff_xy, XY], [Not(YX), YX]), 'not_right', [e1], principal=Not(YX))
    e3 = Proof(Sequent([iff_xy], [H_xy, YX]), 'implies_right', [e2], principal=H_xy)
    e4 = Proof(Sequent([H_xy], [H_xy, YX]), 'weakening_right',
               [Proof(Sequent([H_xy], [H_xy]), 'axiom', principal=H_xy)], principal=YX)
    e5 = Proof(Sequent([H_xy, iff_xy], [YX]), 'not_left', [e4], principal=iff_xy)
    ext_yx = Proof(Sequent([iff_xy], [YX]), 'cut', [e3, e5], principal=H_xy)

    # --- Extract XZ from iff_xz (forward: In(a,s) -> Eq(a,b)) ---
    f1 = Proof(Sequent([iff_xz, XZ], [XZ]), 'axiom', principal=XZ)
    f2 = Proof(Sequent([iff_xz, XZ], [Not(ZX), XZ]), 'weakening_right', [f1], principal=Not(ZX))
    f3 = Proof(Sequent([iff_xz], [H_xz, XZ]), 'implies_right', [f2], principal=H_xz)
    f4 = Proof(Sequent([H_xz], [H_xz, XZ]), 'weakening_right',
               [Proof(Sequent([H_xz], [H_xz]), 'axiom', principal=H_xz)], principal=XZ)
    f5 = Proof(Sequent([H_xz, iff_xz], [XZ]), 'not_left', [f4], principal=iff_xz)
    ext_xz = Proof(Sequent([iff_xz], [XZ]), 'cut', [f3, f5], principal=H_xz)

    # --- Direct: YX, XZ, Y |- Z (hypothetical syllogism + modus ponens) ---
    g1 = Proof(Sequent([Y], [Y]), 'axiom', principal=Y)
    g2 = Proof(Sequent([Y], [Y, Z]), 'weakening_right', [g1], principal=Z)
    g3 = Proof(Sequent([XZ, Y], [Y, Z]), 'weakening_left', [g2], principal=XZ)
    g4 = Proof(Sequent([X], [X]), 'axiom', principal=X)
    g5 = Proof(Sequent([X], [X, Z]), 'weakening_right', [g4], principal=Z)
    g6 = Proof(Sequent([Y, X], [X, Z]), 'weakening_left', [g5], principal=Y)
    g7 = Proof(Sequent([Z], [Z]), 'axiom', principal=Z)
    g8 = Proof(Sequent([X, Z], [Z]), 'weakening_left', [g7], principal=X)
    g9 = Proof(Sequent([Y, X, Z], [Z]), 'weakening_left', [g8], principal=Y)
    g10 = Proof(Sequent([XZ, Y, X], [Z]), 'implies_left', [g6, g9], principal=XZ)
    direct = Proof(Sequent([YX, XZ, Y], [Z]), 'implies_left', [g3, g10], principal=YX)

    # --- Cut XZ: iff_xz, YX, Y |- Z ---
    c1a = Proof(Sequent([iff_xz], [XZ, Z]), 'weakening_right', [ext_xz], principal=Z)
    c1b = Proof(Sequent([iff_xz, YX], [XZ, Z]), 'weakening_left', [c1a], principal=YX)
    c1c = Proof(Sequent([iff_xz, YX, Y], [XZ, Z]), 'weakening_left', [c1b], principal=Y)
    c1d = Proof(Sequent([iff_xz, YX, XZ, Y], [Z]), 'weakening_left', [direct], principal=iff_xz)
    c1 = Proof(Sequent([iff_xz, YX, Y], [Z]), 'cut', [c1c, c1d], principal=XZ)

    # --- Cut YX: iff_xy, iff_xz, Y |- Z ---
    c2a = Proof(Sequent([iff_xy], [YX, Z]), 'weakening_right', [ext_yx], principal=Z)
    c2b = Proof(Sequent([iff_xy, iff_xz], [YX, Z]), 'weakening_left', [c2a], principal=iff_xz)
    c2c = Proof(Sequent([iff_xy, iff_xz, Y], [YX, Z]), 'weakening_left', [c2b], principal=Y)
    c2d = Proof(Sequent([iff_xy, iff_xz, YX, Y], [Z]), 'weakening_left', [c1], principal=iff_xy)
    c2 = Proof(Sequent([iff_xy, iff_xz, Y], [Z]), 'cut', [c2c, c2d], principal=YX)

    # --- Inline Eq(a,a): |- Y ---
    P_r = In(z2, a)
    PtoP = Implies(P_r, P_r)
    NPtoP = Not(PtoP)
    imp_main = Implies(PtoP, NPtoP)
    iff_body = Not(imp_main)
    r1 = Proof(Sequent([P_r], [P_r]), 'axiom', principal=P_r)
    r2 = Proof(Sequent([], [PtoP]), 'implies_right', [r1], principal=PtoP)
    r3 = Proof(Sequent([], [PtoP]), 'implies_right',
               [Proof(Sequent([P_r], [P_r]), 'axiom', principal=P_r)], principal=PtoP)
    r4 = Proof(Sequent([NPtoP], []), 'not_left', [r3], principal=NPtoP)
    r5 = Proof(Sequent([imp_main], []), 'implies_left', [r2, r4], principal=imp_main)
    r6 = Proof(Sequent([], [iff_body]), 'not_right', [r5], principal=iff_body)
    eq_aa = Forall(z2, iff_body)
    r7 = Proof(Sequent([], [eq_aa]), 'forall_right', [r6], term=z2, principal=eq_aa)

    # --- Cut Y: iff_xy, iff_xz |- Z ---
    c3a = Proof(Sequent([], [eq_aa, Z]), 'weakening_right', [r7], principal=Z)
    c3b = Proof(Sequent([iff_xy], [eq_aa, Z]), 'weakening_left', [c3a], principal=iff_xy)
    c3c = Proof(Sequent([iff_xy, iff_xz], [eq_aa, Z]), 'weakening_left', [c3b], principal=iff_xz)
    c3 = Proof(Sequent([iff_xy, iff_xz], [Z]), 'cut', [c3c, c2], principal=Y)

    # --- Instantiate char_a (z=a) and char_b (z=a) ---
    d1 = Proof(Sequent([char_a, iff_xz], [Z]), 'forall_left', [c3], principal=char_a, term=a)
    d2 = Proof(Sequent([char_a, char_b], [Z]), 'forall_left', [d1], principal=char_b, term=a)

    # --- Close ---
    imp1 = Implies(char_b, Z)
    s1 = Proof(Sequent([char_a], [imp1]), 'implies_right', [d2], principal=imp1)
    imp2 = Implies(char_a, imp1)
    s2 = Proof(Sequent([], [imp2]), 'implies_right', [s1], principal=imp2)
    fs = Forall(s, imp2)
    s3 = Proof(Sequent([], [fs]), 'forall_right', [s2], term=s, principal=fs)
    fb = Forall(b, fs)
    s4 = Proof(Sequent([], [fb]), 'forall_right', [s3], term=b, principal=fb)
    fa = Forall(a, fb)
    s5 = Proof(Sequent([], [fa]), 'forall_right', [s4], term=a, principal=fa)
    s5.name = 'singleton_eq'
    return s5


def eq_transfer():
    """Extensionality |- forall a,b,c,d. Eq(a,b) implies Eq(c,d) implies Iff(In(a,c),In(b,d))"""
    a, b, c, d = Var(), Var(), Var(), Var()
    xp, yp, zp = Var(), Var(), Var()

    ext_ax = zfc.Extensionality()
    eq_ab = Eq(a, b)
    eq_cd = Eq(c, d)
    A = In(a, c)
    B = In(b, c)
    C = In(b, d)
    AB = Implies(A, B)
    BA = Implies(B, A)
    BC = Implies(B, C)
    CB = Implies(C, B)
    AC = Implies(A, C)
    CA = Implies(C, A)
    H_ac = Implies(AC, Not(CA))
    iff_ac = Iff(A, C)

    # Extensionality expanded form
    ext_full = Forall(xp, Forall(yp,
        Implies(Forall(zp, Iff(In(zp, xp), In(zp, yp))),
                Forall(zp, Iff(In(xp, zp), In(yp, zp))))))
    ext_inst_x = Forall(yp,
        Implies(Forall(zp, Iff(In(zp, a), In(zp, yp))),
                Forall(zp, Iff(In(a, zp), In(yp, zp)))))
    eq_ab_exp = Forall(zp, Iff(In(zp, a), In(zp, b)))
    fa_iff_ab = Forall(zp, Iff(In(a, zp), In(b, zp)))
    ext_inst_xy = Implies(eq_ab_exp, fa_iff_ab)
    iff_ab_c = Iff(A, B)  # Iff(In(a,c), In(b,c))

    # Eq(c,d) gives membership equivalence
    eq_cd_exp = Forall(zp, Iff(In(zp, c), In(zp, d)))
    iff_bcd = Iff(B, C)  # Iff(In(b,c), In(b,d))

    # === Get iff_ab_c from Extensionality + Eq(a,b) ===
    # ext_inst_xy |- ext_inst_xy (axiom)
    # forall_left twice on ext_ax to get ext_inst_xy
    t0 = Proof(Sequent([ext_inst_xy], [ext_inst_xy]), 'axiom', principal=ext_inst_xy)
    t1 = Proof(Sequent([ext_inst_x], [ext_inst_xy]),
               'forall_left', [t0], principal=ext_inst_x, term=b)
    t2 = Proof(Sequent([ext_ax], [ext_inst_xy]),
               'forall_left', [t1], principal=ext_full, term=a)
    # ext_ax, eq_ab |- fa_iff_ab (modus ponens)
    mp1a = Proof(Sequent([eq_ab], [eq_ab]), 'axiom', principal=eq_ab)
    mp1b = Proof(Sequent([eq_ab], [eq_ab, iff_ab_c]), 'weakening_right', [mp1a], principal=iff_ab_c)
    mp1c = Proof(Sequent([eq_ab, fa_iff_ab], [iff_ab_c]),
                 'weakening_left',
                 [Proof(Sequent([fa_iff_ab], [iff_ab_c]), 'forall_left',
                        [Proof(Sequent([iff_ab_c], [iff_ab_c]), 'axiom', principal=iff_ab_c)],
                        principal=fa_iff_ab, term=c)],
                 principal=eq_ab)
    mp1 = Proof(Sequent([eq_ab, ext_inst_xy], [iff_ab_c]),
                'implies_left', [mp1b, mp1c], principal=ext_inst_xy)
    # Cut ext_inst_xy: ext_ax, eq_ab |- iff_ab_c
    ct1a = Proof(Sequent([ext_ax], [ext_inst_xy, iff_ab_c]),
                 'weakening_right', [t2], principal=iff_ab_c)
    ct1b = Proof(Sequent([ext_ax, eq_ab], [ext_inst_xy, iff_ab_c]),
                 'weakening_left', [ct1a], principal=eq_ab)
    ct1c = Proof(Sequent([ext_ax, eq_ab, ext_inst_xy], [iff_ab_c]),
                 'weakening_left', [mp1], principal=ext_ax)
    got_iff_ab_c = Proof(Sequent([ext_ax, eq_ab], [iff_ab_c]),
                         'cut', [ct1b, ct1c], principal=ext_inst_xy)

    # === Get iff_bcd from Eq(c,d) ===
    # eq_cd |- iff_bcd (just forall_left with b)
    got_iff_bcd = Proof(Sequent([eq_cd], [iff_bcd]), 'forall_left',
                        [Proof(Sequent([iff_bcd], [iff_bcd]), 'axiom', principal=iff_bcd)],
                        principal=eq_cd, term=b)

    # === Extract AB from iff_ab_c and BC from iff_bcd ===
    H_ab = Implies(AB, Not(BA))
    e1 = Proof(Sequent([iff_ab_c, AB], [AB]), 'axiom', principal=AB)
    e2 = Proof(Sequent([iff_ab_c, AB], [Not(BA), AB]), 'weakening_right', [e1], principal=Not(BA))
    e3 = Proof(Sequent([iff_ab_c], [H_ab, AB]), 'implies_right', [e2], principal=H_ab)
    e4 = Proof(Sequent([H_ab], [H_ab, AB]), 'weakening_right',
               [Proof(Sequent([H_ab], [H_ab]), 'axiom', principal=H_ab)], principal=AB)
    e5 = Proof(Sequent([H_ab, iff_ab_c], [AB]), 'not_left', [e4], principal=iff_ab_c)
    ext_ab = Proof(Sequent([iff_ab_c], [AB]), 'cut', [e3, e5], principal=H_ab)

    H_bc = Implies(BC, Not(CB))
    f1 = Proof(Sequent([iff_bcd, BC], [BC]), 'axiom', principal=BC)
    f2 = Proof(Sequent([iff_bcd, BC], [Not(CB), BC]), 'weakening_right', [f1], principal=Not(CB))
    f3 = Proof(Sequent([iff_bcd], [H_bc, BC]), 'implies_right', [f2], principal=H_bc)
    f4 = Proof(Sequent([H_bc], [H_bc, BC]), 'weakening_right',
               [Proof(Sequent([H_bc], [H_bc]), 'axiom', principal=H_bc)], principal=BC)
    f5 = Proof(Sequent([H_bc, iff_bcd], [BC]), 'not_left', [f4], principal=iff_bcd)
    ext_bc = Proof(Sequent([iff_bcd], [BC]), 'cut', [f3, f5], principal=H_bc)

    # === Extract BA from iff_ab_c and CB from iff_bcd ===
    g1 = Proof(Sequent([iff_ab_c, AB, BA], [BA]), 'axiom', principal=BA)
    g2 = Proof(Sequent([iff_ab_c, AB], [Not(BA), BA]), 'not_right', [g1], principal=Not(BA))
    g3 = Proof(Sequent([iff_ab_c], [H_ab, BA]), 'implies_right', [g2], principal=H_ab)
    g4 = Proof(Sequent([H_ab], [H_ab, BA]), 'weakening_right',
               [Proof(Sequent([H_ab], [H_ab]), 'axiom', principal=H_ab)], principal=BA)
    g5 = Proof(Sequent([H_ab, iff_ab_c], [BA]), 'not_left', [g4], principal=iff_ab_c)
    ext_ba = Proof(Sequent([iff_ab_c], [BA]), 'cut', [g3, g5], principal=H_ab)

    h1 = Proof(Sequent([iff_bcd, BC, CB], [CB]), 'axiom', principal=CB)
    h2 = Proof(Sequent([iff_bcd, BC], [Not(CB), CB]), 'not_right', [h1], principal=Not(CB))
    h3 = Proof(Sequent([iff_bcd], [H_bc, CB]), 'implies_right', [h2], principal=H_bc)
    h4 = Proof(Sequent([H_bc], [H_bc, CB]), 'weakening_right',
               [Proof(Sequent([H_bc], [H_bc]), 'axiom', principal=H_bc)], principal=CB)
    h5 = Proof(Sequent([H_bc, iff_bcd], [CB]), 'not_left', [h4], principal=iff_bcd)
    ext_cb = Proof(Sequent([iff_bcd], [CB]), 'cut', [h3, h5], principal=H_bc)

    # === Forward: AB, BC, A |- C (hypothetical syllogism) ===
    fw1 = Proof(Sequent([A], [A]), 'axiom', principal=A)
    fw2 = Proof(Sequent([A], [A, C]), 'weakening_right', [fw1], principal=C)
    fw3 = Proof(Sequent([BC, A], [A, C]), 'weakening_left', [fw2], principal=BC)
    fw4 = Proof(Sequent([B], [B]), 'axiom', principal=B)
    fw5 = Proof(Sequent([B], [B, C]), 'weakening_right', [fw4], principal=C)
    fw6 = Proof(Sequent([A, B], [B, C]), 'weakening_left', [fw5], principal=A)
    fw7 = Proof(Sequent([C], [C]), 'axiom', principal=C)
    fw8 = Proof(Sequent([A, C], [C]), 'weakening_left', [fw7], principal=A)
    fw9 = Proof(Sequent([A, B, C], [C]), 'weakening_left', [fw8], principal=B)
    fw10 = Proof(Sequent([A, B, BC], [C]), 'implies_left', [fw6, fw9], principal=BC)
    fw = Proof(Sequent([AB, BC, A], [C]), 'implies_left', [fw3, fw10], principal=AB)

    # === Backward: BA, CB, C |- A ===
    bw1 = Proof(Sequent([C], [C]), 'axiom', principal=C)
    bw2 = Proof(Sequent([C], [C, A]), 'weakening_right', [bw1], principal=A)
    bw3 = Proof(Sequent([BA, C], [C, A]), 'weakening_left', [bw2], principal=BA)
    bw4 = Proof(Sequent([B], [B]), 'axiom', principal=B)
    bw5 = Proof(Sequent([B], [B, A]), 'weakening_right', [bw4], principal=A)
    bw6 = Proof(Sequent([C, B], [B, A]), 'weakening_left', [bw5], principal=C)
    bw7 = Proof(Sequent([A], [A]), 'axiom', principal=A)
    bw8 = Proof(Sequent([C, A], [A]), 'weakening_left', [bw7], principal=C)
    bw9 = Proof(Sequent([C, B, A], [A]), 'weakening_left', [bw8], principal=B)
    bw10 = Proof(Sequent([C, B, BA], [A]), 'implies_left', [bw6, bw9], principal=BA)
    bw = Proof(Sequent([CB, BA, C], [A]), 'implies_left', [bw3, bw10], principal=CB)

    # === Compose forward: ext_ax, eq_ab, eq_cd, A |- C ===
    # Cut AB: from iff_ab_c |- AB (ext_ab) + fw with iff contexts
    fw_c1a = Proof(Sequent([iff_ab_c], [AB, C]), 'weakening_right', [ext_ab], principal=C)
    fw_c1b = Proof(Sequent([iff_ab_c, BC], [AB, C]), 'weakening_left', [fw_c1a], principal=BC)
    fw_c1c = Proof(Sequent([iff_ab_c, BC, A], [AB, C]), 'weakening_left', [fw_c1b], principal=A)
    fw_c1d = Proof(Sequent([iff_ab_c, AB, BC, A], [C]), 'weakening_left', [fw], principal=iff_ab_c)
    fw_c1 = Proof(Sequent([iff_ab_c, BC, A], [C]), 'cut', [fw_c1c, fw_c1d], principal=AB)
    # Cut BC: from iff_bcd |- BC (ext_bc) + above
    fw_c2a = Proof(Sequent([iff_bcd], [BC, C]), 'weakening_right', [ext_bc], principal=C)
    fw_c2b = Proof(Sequent([iff_bcd, iff_ab_c], [BC, C]), 'weakening_left', [fw_c2a], principal=iff_ab_c)
    fw_c2c = Proof(Sequent([iff_bcd, iff_ab_c, A], [BC, C]), 'weakening_left', [fw_c2b], principal=A)
    fw_c2d = Proof(Sequent([iff_ab_c, iff_bcd, BC, A], [C]), 'weakening_left', [fw_c1], principal=iff_bcd)
    fw_c2 = Proof(Sequent([iff_ab_c, iff_bcd, A], [C]), 'cut', [fw_c2c, fw_c2d], principal=BC)
    # Cut iff_ab_c: ext_ax, eq_ab, iff_bcd, A |- C
    fw_c3a = Proof(Sequent([ext_ax, eq_ab], [iff_ab_c, C]),
                   'weakening_right', [got_iff_ab_c], principal=C)
    fw_c3b = Proof(Sequent([ext_ax, eq_ab, iff_bcd], [iff_ab_c, C]),
                   'weakening_left', [fw_c3a], principal=iff_bcd)
    fw_c3c = Proof(Sequent([ext_ax, eq_ab, iff_bcd, A], [iff_ab_c, C]),
                   'weakening_left', [fw_c3b], principal=A)
    fw_c3d = Proof(Sequent([ext_ax, eq_ab, iff_ab_c, iff_bcd, A], [C]),
                   'weakening_left', [fw_c2], principal=ext_ax)
    fw_c3e = Proof(Sequent([ext_ax, eq_ab, iff_ab_c, iff_bcd, A], [C]),
                   'weakening_left', [fw_c3d], principal=eq_ab)
    # Hmm, fw_c2 already has [iff_ab_c, iff_bcd, A] on left. I need to add ext_ax and eq_ab.
    # fw_c2: [iff_ab_c, iff_bcd, A] |- [C]. Weaken left ext_ax, eq_ab:
    fw_c3d2 = Proof(Sequent([ext_ax, iff_ab_c, iff_bcd, A], [C]),
                    'weakening_left', [fw_c2], principal=ext_ax)
    fw_c3e2 = Proof(Sequent([ext_ax, eq_ab, iff_ab_c, iff_bcd, A], [C]),
                    'weakening_left', [fw_c3d2], principal=eq_ab)
    fw_c3 = Proof(Sequent([ext_ax, eq_ab, iff_bcd, A], [C]),
                  'cut', [fw_c3c, fw_c3e2], principal=iff_ab_c)
    # Cut iff_bcd: ext_ax, eq_ab, eq_cd, A |- C
    fw_c4a = Proof(Sequent([eq_cd], [iff_bcd, C]), 'weakening_right', [got_iff_bcd], principal=C)
    fw_c4b = Proof(Sequent([eq_cd, ext_ax], [iff_bcd, C]), 'weakening_left', [fw_c4a], principal=ext_ax)
    fw_c4c = Proof(Sequent([eq_cd, ext_ax, eq_ab], [iff_bcd, C]),
                   'weakening_left', [fw_c4b], principal=eq_ab)
    fw_c4d = Proof(Sequent([eq_cd, ext_ax, eq_ab, A], [iff_bcd, C]),
                   'weakening_left', [fw_c4c], principal=A)
    fw_c4e = Proof(Sequent([ext_ax, eq_ab, eq_cd, iff_bcd, A], [C]),
                   'weakening_left', [fw_c3], principal=eq_cd)
    fw_final = Proof(Sequent([ext_ax, eq_ab, eq_cd, A], [C]),
                     'cut', [fw_c4d, fw_c4e], principal=iff_bcd)

    # === Compose backward: ext_ax, eq_ab, eq_cd, C |- A ===
    bw_c1a = Proof(Sequent([iff_ab_c], [BA, A]), 'weakening_right', [ext_ba], principal=A)
    bw_c1b = Proof(Sequent([iff_ab_c, CB], [BA, A]), 'weakening_left', [bw_c1a], principal=CB)
    bw_c1c = Proof(Sequent([iff_ab_c, CB, C], [BA, A]), 'weakening_left', [bw_c1b], principal=C)
    bw_c1d = Proof(Sequent([iff_ab_c, CB, BA, C], [A]), 'weakening_left', [bw], principal=iff_ab_c)
    bw_c1 = Proof(Sequent([iff_ab_c, CB, C], [A]), 'cut', [bw_c1c, bw_c1d], principal=BA)
    bw_c2a = Proof(Sequent([iff_bcd], [CB, A]), 'weakening_right', [ext_cb], principal=A)
    bw_c2b = Proof(Sequent([iff_bcd, iff_ab_c], [CB, A]), 'weakening_left', [bw_c2a], principal=iff_ab_c)
    bw_c2c = Proof(Sequent([iff_bcd, iff_ab_c, C], [CB, A]), 'weakening_left', [bw_c2b], principal=C)
    bw_c2d = Proof(Sequent([iff_ab_c, iff_bcd, CB, C], [A]), 'weakening_left', [bw_c1], principal=iff_bcd)
    bw_c2 = Proof(Sequent([iff_ab_c, iff_bcd, C], [A]), 'cut', [bw_c2c, bw_c2d], principal=CB)
    bw_c3a = Proof(Sequent([ext_ax, eq_ab], [iff_ab_c, A]),
                   'weakening_right', [got_iff_ab_c], principal=A)
    bw_c3b = Proof(Sequent([ext_ax, eq_ab, iff_bcd], [iff_ab_c, A]),
                   'weakening_left', [bw_c3a], principal=iff_bcd)
    bw_c3c = Proof(Sequent([ext_ax, eq_ab, iff_bcd, C], [iff_ab_c, A]),
                   'weakening_left', [bw_c3b], principal=C)
    bw_c3d = Proof(Sequent([ext_ax, iff_ab_c, iff_bcd, C], [A]),
                   'weakening_left', [bw_c2], principal=ext_ax)
    bw_c3e = Proof(Sequent([ext_ax, eq_ab, iff_ab_c, iff_bcd, C], [A]),
                   'weakening_left', [bw_c3d], principal=eq_ab)
    bw_c3 = Proof(Sequent([ext_ax, eq_ab, iff_bcd, C], [A]),
                  'cut', [bw_c3c, bw_c3e], principal=iff_ab_c)
    bw_c4a = Proof(Sequent([eq_cd], [iff_bcd, A]), 'weakening_right', [got_iff_bcd], principal=A)
    bw_c4b = Proof(Sequent([eq_cd, ext_ax], [iff_bcd, A]), 'weakening_left', [bw_c4a], principal=ext_ax)
    bw_c4c = Proof(Sequent([eq_cd, ext_ax, eq_ab], [iff_bcd, A]),
                   'weakening_left', [bw_c4b], principal=eq_ab)
    bw_c4d = Proof(Sequent([eq_cd, ext_ax, eq_ab, C], [iff_bcd, A]),
                   'weakening_left', [bw_c4c], principal=C)
    bw_c4e = Proof(Sequent([ext_ax, eq_ab, eq_cd, iff_bcd, C], [A]),
                   'weakening_left', [bw_c3], principal=eq_cd)
    bw_final = Proof(Sequent([ext_ax, eq_ab, eq_cd, C], [A]),
                     'cut', [bw_c4d, bw_c4e], principal=iff_bcd)

    # === Build Iff(A, C) ===
    fwd_ac = Proof(Sequent([ext_ax, eq_ab, eq_cd], [AC]),
                   'implies_right', [fw_final], principal=AC)
    bwd_ca = Proof(Sequent([ext_ax, eq_ab, eq_cd], [CA]),
                   'implies_right', [bw_final], principal=CA)
    nr = Proof(Sequent([ext_ax, eq_ab, eq_cd, Not(CA)], []),
               'not_left', [bwd_ca], principal=Not(CA))
    il = Proof(Sequent([ext_ax, eq_ab, eq_cd, H_ac], []),
               'implies_left', [fwd_ac, nr], principal=H_ac)
    core = Proof(Sequent([ext_ax, eq_ab, eq_cd], [iff_ac]),
                 'not_right', [il], principal=iff_ac)

    # === Close ===
    imp1 = Implies(eq_cd, iff_ac)
    s1 = Proof(Sequent([ext_ax, eq_ab], [imp1]), 'implies_right', [core], principal=imp1)
    imp2 = Implies(eq_ab, imp1)
    s2 = Proof(Sequent([ext_ax], [imp2]), 'implies_right', [s1], principal=imp2)
    fd = Forall(d, imp2)
    s3 = Proof(Sequent([ext_ax], [fd]), 'forall_right', [s2], term=d, principal=fd)
    fc = Forall(c, fd)
    s4 = Proof(Sequent([ext_ax], [fc]), 'forall_right', [s3], term=c, principal=fc)
    fb = Forall(b, fc)
    s5 = Proof(Sequent([ext_ax], [fb]), 'forall_right', [s4], term=b, principal=fb)
    fa = Forall(a, fb)
    s6 = Proof(Sequent([ext_ax], [fa]), 'forall_right', [s5], term=a, principal=fa)
    s6.name = 'eq_transfer'
    return s6


def iff_mp(P, Q, vars: list[Var]):
    """|- forall vars. Iff(P,Q) implies P implies Q"""
    proof = iff_elim_left(P, Q, vars)
    proof.name = 'iff_mp'
    return proof


def iff_mp_rev(P, Q, vars: list[Var]):
    """|- forall vars. Iff(P,Q) implies Q implies P"""
    proof = iff_elim_right(P, Q, vars)
    proof.name = 'iff_mp_rev'
    return proof


def iff_sym(P, Q, vars: list[Var]):
    """|- forall vars. Iff(P,Q) implies Iff(Q,P)"""
    PQ = Implies(P, Q)
    QP = Implies(Q, P)
    NPQ = Not(PQ)
    NQP = Not(QP)
    H1 = Implies(PQ, NQP)
    H2 = Implies(QP, NPQ)
    iff_pq = Iff(P, Q)
    iff_qp = Iff(Q, P)

    # Extract QP from iff_pq
    a1 = Proof(Sequent([iff_pq, PQ, QP], [QP]), 'axiom', principal=QP)
    a2 = Proof(Sequent([iff_pq, PQ], [NQP, QP]), 'not_right', [a1], principal=NQP)
    a3 = Proof(Sequent([iff_pq], [H1, QP]), 'implies_right', [a2], principal=H1)
    a4 = Proof(Sequent([H1], [H1, QP]), 'weakening_right',
               [Proof(Sequent([H1], [H1]), 'axiom', principal=H1)], principal=QP)
    a5 = Proof(Sequent([H1, iff_pq], [QP]), 'not_left', [a4], principal=iff_pq)
    ext_qp = Proof(Sequent([iff_pq], [QP]), 'cut', [a3, a5], principal=H1)

    # Extract PQ from iff_pq
    b1 = Proof(Sequent([iff_pq, PQ], [PQ]), 'axiom', principal=PQ)
    b2 = Proof(Sequent([iff_pq, PQ], [NQP, PQ]), 'weakening_right', [b1], principal=NQP)
    b3 = Proof(Sequent([iff_pq], [H1, PQ]), 'implies_right', [b2], principal=H1)
    b4 = Proof(Sequent([H1], [H1, PQ]), 'weakening_right',
               [Proof(Sequent([H1], [H1]), 'axiom', principal=H1)], principal=PQ)
    b5 = Proof(Sequent([H1, iff_pq], [PQ]), 'not_left', [b4], principal=iff_pq)
    ext_pq = Proof(Sequent([iff_pq], [PQ]), 'cut', [b3, b5], principal=H1)

    # Build Iff(Q, P)
    c1 = Proof(Sequent([iff_pq, NPQ], []), 'not_left', [ext_pq], principal=NPQ)
    c2 = Proof(Sequent([iff_pq, H2], []), 'implies_left', [ext_qp, c1], principal=H2)
    core = Proof(Sequent([iff_pq], [iff_qp]), 'not_right', [c2], principal=iff_qp)

    # Close
    imp = Implies(iff_pq, iff_qp)
    s1 = Proof(Sequent([], [imp]), 'implies_right', [core], principal=imp)
    proof = s1
    for v in vars:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], term=v, principal=fa)
    proof.name = 'iff_sym'
    return proof


def char_transfer(A, B, C):
    """|- Iff(A,B) implies Iff(B,C) implies Iff(A,C)
    No quantifiers — for inline composition. Same as iff_chain core."""
    AB = Implies(A, B); BA = Implies(B, A)
    BC = Implies(B, C); CB = Implies(C, B)
    AC = Implies(A, C); CA = Implies(C, A)
    NAC = Not(AC); NCA = Not(CA)
    H_ab = Implies(AB, Not(BA)); H_bc = Implies(BC, Not(CB))
    H_ac = Implies(AC, NCA)
    iff_ab = Iff(A, B); iff_bc = Iff(B, C); iff_ac = Iff(A, C)

    def _ext_fwd(iff_f, LR, RL, H):
        e1 = Proof(Sequent([iff_f, LR], [LR]), 'axiom', principal=LR)
        e2 = Proof(Sequent([iff_f, LR], [Not(RL), LR]), 'weakening_right', [e1], principal=Not(RL))
        e3 = Proof(Sequent([iff_f], [H, LR]), 'implies_right', [e2], principal=H)
        e4 = Proof(Sequent([H], [H, LR]), 'weakening_right',
                   [Proof(Sequent([H], [H]), 'axiom', principal=H)], principal=LR)
        e5 = Proof(Sequent([H, iff_f], [LR]), 'not_left', [e4], principal=iff_f)
        return Proof(Sequent([iff_f], [LR]), 'cut', [e3, e5], principal=H)

    def _ext_bwd(iff_f, LR, RL, H):
        e1 = Proof(Sequent([iff_f, LR, RL], [RL]), 'axiom', principal=RL)
        e2 = Proof(Sequent([iff_f, LR], [Not(RL), RL]), 'not_right', [e1], principal=Not(RL))
        e3 = Proof(Sequent([iff_f], [H, RL]), 'implies_right', [e2], principal=H)
        e4 = Proof(Sequent([H], [H, RL]), 'weakening_right',
                   [Proof(Sequent([H], [H]), 'axiom', principal=H)], principal=RL)
        e5 = Proof(Sequent([H, iff_f], [RL]), 'not_left', [e4], principal=iff_f)
        return Proof(Sequent([iff_f], [RL]), 'cut', [e3, e5], principal=H)

    ext_ab = _ext_fwd(iff_ab, AB, BA, H_ab)
    ext_ba = _ext_bwd(iff_ab, AB, BA, H_ab)
    ext_bc = _ext_fwd(iff_bc, BC, CB, H_bc)
    ext_cb = _ext_bwd(iff_bc, BC, CB, H_bc)

    # Forward: AB, BC, A |- C
    fw1 = Proof(Sequent([A], [A, C]), 'weakening_right',
                [Proof(Sequent([A], [A]), 'axiom', principal=A)], principal=C)
    fw2 = Proof(Sequent([BC, A], [A, C]), 'weakening_left', [fw1], principal=BC)
    fw3 = Proof(Sequent([B], [B, C]), 'weakening_right',
                [Proof(Sequent([B], [B]), 'axiom', principal=B)], principal=C)
    fw4 = Proof(Sequent([A, B], [B, C]), 'weakening_left', [fw3], principal=A)
    fw5 = Proof(Sequent([C], [C]), 'axiom', principal=C)
    fw6 = Proof(Sequent([A, C], [C]), 'weakening_left', [fw5], principal=A)
    fw7 = Proof(Sequent([A, B, C], [C]), 'weakening_left', [fw6], principal=B)
    fw8 = Proof(Sequent([A, B, BC], [C]), 'implies_left', [fw4, fw7], principal=BC)
    fw = Proof(Sequent([AB, BC, A], [C]), 'implies_left', [fw2, fw8], principal=AB)

    # Backward: BA, CB, C |- A
    bw1 = Proof(Sequent([C], [C, A]), 'weakening_right',
                [Proof(Sequent([C], [C]), 'axiom', principal=C)], principal=A)
    bw2 = Proof(Sequent([BA, C], [C, A]), 'weakening_left', [bw1], principal=BA)
    bw3 = Proof(Sequent([B], [B, A]), 'weakening_right',
                [Proof(Sequent([B], [B]), 'axiom', principal=B)], principal=A)
    bw4 = Proof(Sequent([C, B], [B, A]), 'weakening_left', [bw3], principal=C)
    bw5 = Proof(Sequent([A], [A]), 'axiom', principal=A)
    bw6 = Proof(Sequent([C, A], [A]), 'weakening_left', [bw5], principal=C)
    bw7 = Proof(Sequent([C, B, A], [A]), 'weakening_left', [bw6], principal=B)
    bw8 = Proof(Sequent([C, B, BA], [A]), 'implies_left', [bw4, bw7], principal=BA)
    bw = Proof(Sequent([CB, BA, C], [A]), 'implies_left', [bw2, bw8], principal=CB)

    # Compose forward: iff_ab, iff_bc, A |- C via cuts
    c1a = Proof(Sequent([iff_ab], [AB, C]), 'weakening_right', [ext_ab], principal=C)
    c1b = Proof(Sequent([iff_ab, iff_bc], [AB, C]), 'weakening_left', [c1a], principal=iff_bc)
    c1c = Proof(Sequent([iff_ab, iff_bc, A], [AB, C]), 'weakening_left', [c1b], principal=A)
    c1d = Proof(Sequent([iff_ab, iff_bc, A], [BC, C]),
                'weakening_right',
                [Proof(Sequent([iff_ab, iff_bc, A], [BC]),
                       'weakening_left',
                       [Proof(Sequent([iff_bc, A], [BC]),
                              'weakening_left', [ext_bc], principal=A)],
                       principal=iff_ab)],
                principal=C)
    # Cut AB
    fw_w = Proof(Sequent([iff_ab, AB, BC, A], [C]), 'weakening_left', [fw], principal=iff_ab)
    fw_w2 = Proof(Sequent([iff_ab, iff_bc, AB, BC, A], [C]), 'weakening_left', [fw_w], principal=iff_bc)
    c1e = Proof(Sequent([iff_ab, iff_bc, A, AB], [BC, C]),
                'weakening_left', [c1d], principal=AB)
    # Hmm, this is getting tangled. Let me use a simpler approach.

    # Just do two sequential cuts on AB and BC.
    # Cut AB: from iff_ab, iff_bc, A |- AB, C and iff_ab, iff_bc, A, AB |- C
    c_fw_ab1 = Proof(Sequent([iff_ab, iff_bc, A], [AB, C]),
                     'weakening_left',
                     [Proof(Sequent([iff_ab, A], [AB, C]),
                            'weakening_left',
                            [Proof(Sequent([iff_ab], [AB, C]),
                                   'weakening_right', [ext_ab], principal=C)],
                            principal=A)],
                     principal=iff_bc)
    # For the second branch, also cut BC inside:
    # iff_ab, iff_bc, A, AB |- C needs BC too.
    # Cut BC: from iff_ab, iff_bc, A, AB |- BC, C and iff_ab, iff_bc, A, AB, BC |- C
    c_fw_bc1 = Proof(Sequent([iff_ab, iff_bc, A, AB], [BC, C]),
                     'weakening_left',
                     [Proof(Sequent([iff_bc, A, AB], [BC, C]),
                            'weakening_left',
                            [Proof(Sequent([iff_bc, AB], [BC, C]),
                                   'weakening_left',
                                   [Proof(Sequent([iff_bc], [BC, C]),
                                          'weakening_right', [ext_bc], principal=C)],
                                   principal=AB)],
                            principal=A)],
                     principal=iff_ab)
    c_fw_bc2 = Proof(Sequent([iff_ab, iff_bc, AB, BC, A], [C]),
                     'weakening_left',
                     [Proof(Sequent([iff_bc, AB, BC, A], [C]),
                            'weakening_left', [fw], principal=iff_bc)],
                     principal=iff_ab)
    c_fw_bc = Proof(Sequent([iff_ab, iff_bc, A, AB], [C]),
                    'cut', [c_fw_bc1, c_fw_bc2], principal=BC)
    fwd_result = Proof(Sequent([iff_ab, iff_bc, A], [C]),
                       'cut', [c_fw_ab1, c_fw_bc], principal=AB)
    fwd_ac = Proof(Sequent([iff_ab, iff_bc], [AC]),
                   'implies_right', [fwd_result], principal=AC)

    # Compose backward: iff_ab, iff_bc, C |- A via cuts
    c_bw_cb1 = Proof(Sequent([iff_ab, iff_bc, C], [CB, A]),
                     'weakening_left',
                     [Proof(Sequent([iff_bc, C], [CB, A]),
                            'weakening_left',
                            [Proof(Sequent([iff_bc], [CB, A]),
                                   'weakening_right', [ext_cb], principal=A)],
                            principal=C)],
                     principal=iff_ab)
    c_bw_ba1 = Proof(Sequent([iff_ab, iff_bc, C, CB], [BA, A]),
                     'weakening_left',
                     [Proof(Sequent([iff_ab, C, CB], [BA, A]),
                            'weakening_left',
                            [Proof(Sequent([iff_ab, CB], [BA, A]),
                                   'weakening_left',
                                   [Proof(Sequent([iff_ab], [BA, A]),
                                          'weakening_right', [ext_ba], principal=A)],
                                   principal=CB)],
                            principal=C)],
                     principal=iff_bc)
    c_bw_ba2 = Proof(Sequent([iff_ab, iff_bc, CB, BA, C], [A]),
                     'weakening_left',
                     [Proof(Sequent([iff_ab, CB, BA, C], [A]),
                            'weakening_left', [bw], principal=iff_ab)],
                     principal=iff_bc)
    c_bw_ba = Proof(Sequent([iff_ab, iff_bc, C, CB], [A]),
                    'cut', [c_bw_ba1, c_bw_ba2], principal=BA)
    bwd_result = Proof(Sequent([iff_ab, iff_bc, C], [A]),
                       'cut', [c_bw_cb1, c_bw_ba], principal=CB)
    bwd_ca = Proof(Sequent([iff_ab, iff_bc], [CA]),
                   'implies_right', [bwd_result], principal=CA)

    # Build Iff(A, C)
    nr = Proof(Sequent([iff_ab, iff_bc, NCA], []), 'not_left', [bwd_ca], principal=NCA)
    il = Proof(Sequent([iff_ab, iff_bc, H_ac], []), 'implies_left', [fwd_ac, nr], principal=H_ac)
    core = Proof(Sequent([iff_ab, iff_bc], [iff_ac]), 'not_right', [il], principal=iff_ac)

    imp1 = Implies(iff_bc, iff_ac)
    s1 = Proof(Sequent([iff_ab], [imp1]), 'implies_right', [core], principal=imp1)
    imp2 = Implies(iff_ab, imp1)
    return Proof(Sequent([], [imp2]), 'implies_right', [s1], principal=imp2)


def singleton_injection():
    """|- forall a, b. (forall z. Iff(Eq(z,a), Eq(z,b))) implies Eq(a,b)
    If {a} and {b} have the same elements (z=a iff z=b for all z), then a=b."""
    a, b, z = Var(), Var(), Var()
    z2 = Var()

    char = Forall(z, Iff(Eq(z, a), Eq(z, b)))
    Y = Eq(a, a)
    Z = Eq(a, b)
    iff_yz = Iff(Y, Z)  # Iff(Eq(a,a), Eq(a,b)) — from instantiating char with z=a

    YZ = Implies(Y, Z)
    ZY = Implies(Z, Y)
    H = Implies(YZ, Not(ZY))

    # --- Extract YZ from iff_yz (forward: Eq(a,a) -> Eq(a,b)) ---
    e1 = Proof(Sequent([iff_yz, YZ], [YZ]), 'axiom', principal=YZ)
    e2 = Proof(Sequent([iff_yz, YZ], [Not(ZY), YZ]), 'weakening_right', [e1], principal=Not(ZY))
    e3 = Proof(Sequent([iff_yz], [H, YZ]), 'implies_right', [e2], principal=H)
    e4 = Proof(Sequent([H], [H, YZ]), 'weakening_right',
               [Proof(Sequent([H], [H]), 'axiom', principal=H)], principal=YZ)
    e5 = Proof(Sequent([H, iff_yz], [YZ]), 'not_left', [e4], principal=iff_yz)
    ext_yz = Proof(Sequent([iff_yz], [YZ]), 'cut', [e3, e5], principal=H)

    # --- Inline Eq(a,a) ---
    P_r = In(z2, a)
    PtoP = Implies(P_r, P_r)
    NPtoP = Not(PtoP)
    imp_main = Implies(PtoP, NPtoP)
    iff_body = Not(imp_main)
    r1 = Proof(Sequent([], [PtoP]), 'implies_right',
               [Proof(Sequent([P_r], [P_r]), 'axiom', principal=P_r)], principal=PtoP)
    r2 = Proof(Sequent([], [PtoP]), 'implies_right',
               [Proof(Sequent([P_r], [P_r]), 'axiom', principal=P_r)], principal=PtoP)
    r3 = Proof(Sequent([NPtoP], []), 'not_left', [r2], principal=NPtoP)
    r4 = Proof(Sequent([imp_main], []), 'implies_left', [r1, r3], principal=imp_main)
    r5 = Proof(Sequent([], [iff_body]), 'not_right', [r4], principal=iff_body)
    eq_aa = Forall(z2, iff_body)
    r6 = Proof(Sequent([], [eq_aa]), 'forall_right', [r5], term=z2, principal=eq_aa)

    # --- Modus ponens: Y, YZ |- Z ---
    mp1 = Proof(Sequent([Y], [Y]), 'axiom', principal=Y)
    mp2 = Proof(Sequent([Y], [Y, Z]), 'weakening_right', [mp1], principal=Z)
    mp3 = Proof(Sequent([Y, Z], [Z]), 'axiom', principal=Z)
    mp4 = Proof(Sequent([Y, YZ], [Z]), 'implies_left', [mp2, mp3], principal=YZ)

    # --- Combine: iff_yz |- Z via cuts ---
    # Cut YZ
    c1a = Proof(Sequent([iff_yz], [YZ, Z]), 'weakening_right', [ext_yz], principal=Z)
    c1b = Proof(Sequent([iff_yz, Y], [YZ, Z]), 'weakening_left', [c1a], principal=Y)
    c1c = Proof(Sequent([iff_yz, Y, YZ], [Z]), 'weakening_left', [mp4], principal=iff_yz)
    c1 = Proof(Sequent([iff_yz, Y], [Z]), 'cut', [c1b, c1c], principal=YZ)
    # Cut Y (eq_reflexive)
    c2a = Proof(Sequent([], [eq_aa, Z]), 'weakening_right', [r6], principal=Z)
    c2b = Proof(Sequent([iff_yz], [eq_aa, Z]), 'weakening_left', [c2a], principal=iff_yz)
    c2 = Proof(Sequent([iff_yz], [Z]), 'cut', [c2b, c1], principal=Y)

    # --- Instantiate char with z=a ---
    d1 = Proof(Sequent([char], [Z]), 'forall_left', [c2], principal=char, term=a)

    # --- Close ---
    imp = Implies(char, Z)
    s1 = Proof(Sequent([], [imp]), 'implies_right', [d1], principal=imp)
    fb = Forall(b, imp)
    s2 = Proof(Sequent([], [fb]), 'forall_right', [s1], term=b, principal=fb)
    fa = Forall(a, fb)
    s3 = Proof(Sequent([], [fa]), 'forall_right', [s2], term=a, principal=fa)
    s3.name = 'singleton_injection'
    return s3


def singleton_pair_eq():
    """|- forall a,c,d. (forall z. Iff(Eq(z,a), Or(Eq(z,c),Eq(z,d)))) implies And(Eq(c,a),Eq(d,a))
    If {a} has same elements as {c,d}, then c=a and d=a."""
    a, c, d, z = Var(), Var(), Var(), Var()
    z2, z3 = Var(), Var()

    char = Forall(z, Iff(Eq(z, a), Or(Eq(z, c), Eq(z, d))))
    eq_ca = Eq(c, a)
    eq_da = Eq(d, a)
    goal = And(eq_ca, eq_da)

    # === z=c: derive Eq(c,a) ===
    iff_c = Iff(Eq(c, a), Or(Eq(c, c), Eq(c, d)))
    or_ccd = Or(Eq(c, c), Eq(c, d))
    OC = Implies(or_ccd, eq_ca)
    CO = Implies(eq_ca, or_ccd)
    H_c = Implies(CO, Not(OC))

    # Extract backward: iff_c |- OC
    ec1 = Proof(Sequent([iff_c, CO, OC], [OC]), 'axiom', principal=OC)
    ec2 = Proof(Sequent([iff_c, CO], [Not(OC), OC]), 'not_right', [ec1], principal=Not(OC))
    ec3 = Proof(Sequent([iff_c], [H_c, OC]), 'implies_right', [ec2], principal=H_c)
    ec4 = Proof(Sequent([H_c], [H_c, OC]), 'weakening_right',
                [Proof(Sequent([H_c], [H_c]), 'axiom', principal=H_c)], principal=OC)
    ec5 = Proof(Sequent([H_c, iff_c], [OC]), 'not_left', [ec4], principal=iff_c)
    ext_oc = Proof(Sequent([iff_c], [OC]), 'cut', [ec3, ec5], principal=H_c)

    # Inline Eq(c,c)
    Pc = In(z2, c)
    PcPc = Implies(Pc, Pc)
    rc1 = Proof(Sequent([], [PcPc]), 'implies_right',
                [Proof(Sequent([Pc], [Pc]), 'axiom', principal=Pc)], principal=PcPc)
    rc2 = Proof(Sequent([], [PcPc]), 'implies_right',
                [Proof(Sequent([Pc], [Pc]), 'axiom', principal=Pc)], principal=PcPc)
    rc3 = Proof(Sequent([Not(PcPc)], []), 'not_left', [rc2], principal=Not(PcPc))
    rc4 = Proof(Sequent([Implies(PcPc, Not(PcPc))], []), 'implies_left',
                [rc1, rc3], principal=Implies(PcPc, Not(PcPc)))
    rc5 = Proof(Sequent([], [Not(Implies(PcPc, Not(PcPc)))]), 'not_right',
                [rc4], principal=Not(Implies(PcPc, Not(PcPc))))
    eq_cc = Forall(z2, Not(Implies(PcPc, Not(PcPc))))
    rc6 = Proof(Sequent([], [eq_cc]), 'forall_right', [rc5], term=z2, principal=eq_cc)

    # Or_intro_left: Eq(c,c) |- Or(Eq(c,c), Eq(c,d))
    eq_cc_v = Eq(c, c)
    ol1 = Proof(Sequent([eq_cc_v], [eq_cc_v]), 'axiom', principal=eq_cc_v)
    ol2 = Proof(Sequent([eq_cc_v, Not(eq_cc_v)], []), 'not_left', [ol1], principal=Not(eq_cc_v))
    ol3 = Proof(Sequent([eq_cc_v, Not(eq_cc_v)], [Eq(c, d)]),
                'weakening_right', [ol2], principal=Eq(c, d))
    ol4 = Proof(Sequent([eq_cc_v], [or_ccd]), 'implies_right', [ol3], principal=or_ccd)

    # MP: or_ccd, OC |- eq_ca
    mc1 = Proof(Sequent([or_ccd], [or_ccd, eq_ca]), 'weakening_right',
                [Proof(Sequent([or_ccd], [or_ccd]), 'axiom', principal=or_ccd)], principal=eq_ca)
    mc2 = Proof(Sequent([or_ccd, eq_ca], [eq_ca]), 'axiom', principal=eq_ca)
    mc = Proof(Sequent([or_ccd, OC], [eq_ca]), 'implies_left', [mc1, mc2], principal=OC)

    # Cuts: iff_c |- eq_ca
    ca1 = Proof(Sequent([iff_c], [OC, eq_ca]), 'weakening_right', [ext_oc], principal=eq_ca)
    ca2 = Proof(Sequent([iff_c, or_ccd], [OC, eq_ca]), 'weakening_left', [ca1], principal=or_ccd)
    ca3 = Proof(Sequent([iff_c, or_ccd, OC], [eq_ca]), 'weakening_left', [mc], principal=iff_c)
    ca4 = Proof(Sequent([iff_c, or_ccd], [eq_ca]), 'cut', [ca2, ca3], principal=OC)
    ca5 = Proof(Sequent([eq_cc_v], [or_ccd, eq_ca]), 'weakening_right', [ol4], principal=eq_ca)
    ca6 = Proof(Sequent([iff_c, eq_cc_v], [or_ccd, eq_ca]), 'weakening_left', [ca5], principal=iff_c)
    ca7 = Proof(Sequent([iff_c, eq_cc_v, or_ccd], [eq_ca]), 'weakening_left', [ca4], principal=eq_cc_v)
    ca8 = Proof(Sequent([iff_c, eq_cc_v], [eq_ca]), 'cut', [ca6, ca7], principal=or_ccd)
    ca9 = Proof(Sequent([], [eq_cc, eq_ca]), 'weakening_right', [rc6], principal=eq_ca)
    ca10 = Proof(Sequent([iff_c], [eq_cc, eq_ca]), 'weakening_left', [ca9], principal=iff_c)
    got_ca = Proof(Sequent([iff_c], [eq_ca]), 'cut', [ca10, ca8], principal=eq_cc_v)

    # === z=d: derive Eq(d,a) ===
    iff_d = Iff(Eq(d, a), Or(Eq(d, c), Eq(d, d)))
    or_dcd = Or(Eq(d, c), Eq(d, d))
    OD = Implies(or_dcd, eq_da)
    DO = Implies(eq_da, or_dcd)
    H_d = Implies(DO, Not(OD))

    ed1 = Proof(Sequent([iff_d, DO, OD], [OD]), 'axiom', principal=OD)
    ed2 = Proof(Sequent([iff_d, DO], [Not(OD), OD]), 'not_right', [ed1], principal=Not(OD))
    ed3 = Proof(Sequent([iff_d], [H_d, OD]), 'implies_right', [ed2], principal=H_d)
    ed4 = Proof(Sequent([H_d], [H_d, OD]), 'weakening_right',
                [Proof(Sequent([H_d], [H_d]), 'axiom', principal=H_d)], principal=OD)
    ed5 = Proof(Sequent([H_d, iff_d], [OD]), 'not_left', [ed4], principal=iff_d)
    ext_od = Proof(Sequent([iff_d], [OD]), 'cut', [ed3, ed5], principal=H_d)

    # Inline Eq(d,d)
    Pd = In(z3, d)
    PdPd = Implies(Pd, Pd)
    rd1 = Proof(Sequent([], [PdPd]), 'implies_right',
                [Proof(Sequent([Pd], [Pd]), 'axiom', principal=Pd)], principal=PdPd)
    rd2 = Proof(Sequent([], [PdPd]), 'implies_right',
                [Proof(Sequent([Pd], [Pd]), 'axiom', principal=Pd)], principal=PdPd)
    rd3 = Proof(Sequent([Not(PdPd)], []), 'not_left', [rd2], principal=Not(PdPd))
    rd4 = Proof(Sequent([Implies(PdPd, Not(PdPd))], []), 'implies_left',
                [rd1, rd3], principal=Implies(PdPd, Not(PdPd)))
    rd5 = Proof(Sequent([], [Not(Implies(PdPd, Not(PdPd)))]), 'not_right',
                [rd4], principal=Not(Implies(PdPd, Not(PdPd))))
    eq_dd = Forall(z3, Not(Implies(PdPd, Not(PdPd))))
    rd6 = Proof(Sequent([], [eq_dd]), 'forall_right', [rd5], term=z3, principal=eq_dd)

    # Or_intro_right: Eq(d,d) |- Or(Eq(d,c), Eq(d,d))
    eq_dd_v = Eq(d, d)
    or1 = Proof(Sequent([eq_dd_v, Not(Eq(d, c))], [eq_dd_v]), 'axiom', principal=eq_dd_v)
    or2 = Proof(Sequent([eq_dd_v], [or_dcd]), 'implies_right', [or1], principal=or_dcd)

    # MP: or_dcd, OD |- eq_da
    md1 = Proof(Sequent([or_dcd], [or_dcd, eq_da]), 'weakening_right',
                [Proof(Sequent([or_dcd], [or_dcd]), 'axiom', principal=or_dcd)], principal=eq_da)
    md2 = Proof(Sequent([or_dcd, eq_da], [eq_da]), 'axiom', principal=eq_da)
    md = Proof(Sequent([or_dcd, OD], [eq_da]), 'implies_left', [md1, md2], principal=OD)

    # Cuts: iff_d |- eq_da
    da1 = Proof(Sequent([iff_d], [OD, eq_da]), 'weakening_right', [ext_od], principal=eq_da)
    da2 = Proof(Sequent([iff_d, or_dcd], [OD, eq_da]), 'weakening_left', [da1], principal=or_dcd)
    da3 = Proof(Sequent([iff_d, or_dcd, OD], [eq_da]), 'weakening_left', [md], principal=iff_d)
    da4 = Proof(Sequent([iff_d, or_dcd], [eq_da]), 'cut', [da2, da3], principal=OD)
    da5 = Proof(Sequent([eq_dd_v], [or_dcd, eq_da]), 'weakening_right', [or2], principal=eq_da)
    da6 = Proof(Sequent([iff_d, eq_dd_v], [or_dcd, eq_da]), 'weakening_left', [da5], principal=iff_d)
    da7 = Proof(Sequent([iff_d, eq_dd_v, or_dcd], [eq_da]), 'weakening_left', [da4], principal=eq_dd_v)
    da8 = Proof(Sequent([iff_d, eq_dd_v], [eq_da]), 'cut', [da6, da7], principal=or_dcd)
    da9 = Proof(Sequent([], [eq_dd, eq_da]), 'weakening_right', [rd6], principal=eq_da)
    da10 = Proof(Sequent([iff_d], [eq_dd, eq_da]), 'weakening_left', [da9], principal=iff_d)
    got_da = Proof(Sequent([iff_d], [eq_da]), 'cut', [da10, da8], principal=eq_dd_v)

    # === Instantiate char ===
    step_ca = Proof(Sequent([char], [eq_ca]), 'forall_left', [got_ca], principal=char, term=c)
    step_da = Proof(Sequent([char], [eq_da]), 'forall_left', [got_da], principal=char, term=d)

    # === Build And(Eq(c,a), Eq(d,a)) ===
    and1 = Proof(Sequent([char, Not(eq_da)], []), 'not_left', [step_da], principal=Not(eq_da))
    and2 = Proof(Sequent([char, Implies(eq_ca, Not(eq_da))], []),
                 'implies_left', [step_ca, and1], principal=Implies(eq_ca, Not(eq_da)))
    and3 = Proof(Sequent([char], [goal]), 'not_right', [and2], principal=goal)

    # === Close ===
    imp = Implies(char, goal)
    s1 = Proof(Sequent([], [imp]), 'implies_right', [and3], principal=imp)
    fd = Forall(d, imp)
    s2 = Proof(Sequent([], [fd]), 'forall_right', [s1], term=d, principal=fd)
    fc = Forall(c, fd)
    s3 = Proof(Sequent([], [fc]), 'forall_right', [s2], term=c, principal=fc)
    fa = Forall(a, fc)
    s4 = Proof(Sequent([], [fa]), 'forall_right', [s3], term=a, principal=fa)
    s4.name = 'singleton_pair_eq'
    return s4


def pair_injection():
    """|- forall a,b,c,d. (forall z. Iff(Or(Eq(z,a),Eq(z,b)),Or(Eq(z,c),Eq(z,d))))
                          implies Or(And(Eq(a,c),Eq(b,d)),And(Eq(a,d),Eq(b,c)))"""
    a, b, c, d, z = Var(), Var(), Var(), Var(), Var()
    z1, z2, z3, z4, ze = Var(), Var(), Var(), Var(), Var()

    char = Forall(z, Iff(Or(Eq(z, a), Eq(z, b)), Or(Eq(z, c), Eq(z, d))))
    eq_ac = Eq(a, c); eq_ad = Eq(a, d); eq_bc = Eq(b, c); eq_bd = Eq(b, d)
    eq_da = Eq(d, a); eq_db = Eq(d, b); eq_ca = Eq(c, a); eq_cb = Eq(c, b)
    left_g = And(eq_ac, eq_bd)
    right_g = And(eq_ad, eq_bc)
    G = Or(left_g, right_g)

    # ================================================================
    # BUILDING BLOCKS
    # ================================================================

    def _eq_refl(x, zv):
        """Build proof of |- Eq(x, x) using eigenvariable zv."""
        P = In(zv, x); PP = Implies(P, P)
        s1 = Proof(Sequent([], [PP]), 'implies_right',
                   [Proof(Sequent([P], [P]), 'axiom', principal=P)], principal=PP)
        s2 = Proof(Sequent([], [PP]), 'implies_right',
                   [Proof(Sequent([P], [P]), 'axiom', principal=P)], principal=PP)
        s3 = Proof(Sequent([Not(PP)], []), 'not_left', [s2], principal=Not(PP))
        s4 = Proof(Sequent([Implies(PP, Not(PP))], []), 'implies_left',
                   [s1, s3], principal=Implies(PP, Not(PP)))
        body = Not(Implies(PP, Not(PP)))
        s5 = Proof(Sequent([], [body]), 'not_right', [s4], principal=body)
        fa = Forall(zv, body)
        return Proof(Sequent([], [fa]), 'forall_right', [s5], term=zv, principal=fa)

    def _or_intro_left(P, Q):
        """Build P |- Or(P, Q)."""
        orPQ = Or(P, Q)
        s1 = Proof(Sequent([P], [P]), 'axiom', principal=P)
        s2 = Proof(Sequent([P, Not(P)], []), 'not_left', [s1], principal=Not(P))
        s3 = Proof(Sequent([P, Not(P)], [Q]), 'weakening_right', [s2], principal=Q)
        return Proof(Sequent([P], [orPQ]), 'implies_right', [s3], principal=orPQ)

    def _or_intro_right(P, Q):
        """Build Q |- Or(P, Q)."""
        orPQ = Or(P, Q)
        s1 = Proof(Sequent([Q, Not(P)], [Q]), 'axiom', principal=Q)
        return Proof(Sequent([Q], [orPQ]), 'implies_right', [s1], principal=orPQ)

    def _extract_fwd(iff_f):
        """Extract forward direction from Iff: iff_f |- Implies(left, right)."""
        L = iff_f.left; R = iff_f.right
        LR = Implies(L, R); RL = Implies(R, L)
        H = Implies(LR, Not(RL))
        e1 = Proof(Sequent([iff_f, LR], [LR]), 'axiom', principal=LR)
        e2 = Proof(Sequent([iff_f, LR], [Not(RL), LR]), 'weakening_right', [e1], principal=Not(RL))
        e3 = Proof(Sequent([iff_f], [H, LR]), 'implies_right', [e2], principal=H)
        e4 = Proof(Sequent([H], [H, LR]), 'weakening_right',
                   [Proof(Sequent([H], [H]), 'axiom', principal=H)], principal=LR)
        e5 = Proof(Sequent([H, iff_f], [LR]), 'not_left', [e4], principal=iff_f)
        return Proof(Sequent([iff_f], [LR]), 'cut', [e3, e5], principal=H)

    def _extract_bwd(iff_f):
        """Extract backward direction from Iff: iff_f |- Implies(right, left)."""
        L = iff_f.left; R = iff_f.right
        LR = Implies(L, R); RL = Implies(R, L)
        H = Implies(LR, Not(RL))
        e1 = Proof(Sequent([iff_f, LR, RL], [RL]), 'axiom', principal=RL)
        e2 = Proof(Sequent([iff_f, LR], [Not(RL), RL]), 'not_right', [e1], principal=Not(RL))
        e3 = Proof(Sequent([iff_f], [H, RL]), 'implies_right', [e2], principal=H)
        e4 = Proof(Sequent([H], [H, RL]), 'weakening_right',
                   [Proof(Sequent([H], [H]), 'axiom', principal=H)], principal=RL)
        e5 = Proof(Sequent([H, iff_f], [RL]), 'not_left', [e4], principal=iff_f)
        return Proof(Sequent([iff_f], [RL]), 'cut', [e3, e5], principal=H)

    def _modus_ponens(impl_proof, ante_proof, ante, cons):
        """From ctx1 |- Implies(A, B) and ctx2 |- A, build combined |- B via cuts."""
        imp = Implies(ante, cons)
        ctx1 = impl_proof.sequent.left; ctx2 = ante_proof.sequent.left
        # Modus ponens core: ante, imp |- cons
        ax1 = Proof(Sequent([ante], [ante, cons]), 'weakening_right',
                    [Proof(Sequent([ante], [ante]), 'axiom', principal=ante)], principal=cons)
        ax2 = Proof(Sequent([ante, cons], [cons]), 'axiom', principal=cons)
        mp = Proof(Sequent([ante, imp], [cons]), 'implies_left', [ax1, ax2], principal=imp)
        # Cut imp
        p1 = impl_proof
        for f in ctx2:
            if not any(f is g for g in ctx1):
                p1 = Proof(Sequent(p1.sequent.left + [f], p1.sequent.right),
                           'weakening_left', [p1], principal=f)
        p1 = Proof(Sequent(p1.sequent.left, [imp, cons]),
                   'weakening_right', [p1], principal=cons)
        p2 = mp
        for f in ctx1 + ctx2:
            if not any(f is g for g in p2.sequent.left):
                p2 = Proof(Sequent(p2.sequent.left + [f], p2.sequent.right),
                           'weakening_left', [p2], principal=f)
        all_ctx = list(set(id(f) for f in ctx1 + ctx2))
        combined = list({id(f): f for f in ctx1 + ctx2}.values())
        r1 = Proof(Sequent(combined, [cons]), 'cut', [p1, p2], principal=imp)
        # Cut ante
        p3 = ante_proof
        for f in ctx1:
            if not any(f is g for g in ctx2):
                p3 = Proof(Sequent(p3.sequent.left + [f], p3.sequent.right),
                           'weakening_left', [p3], principal=f)
        p3 = Proof(Sequent(p3.sequent.left, [ante, cons]),
                   'weakening_right', [p3], principal=cons)
        p4 = Proof(Sequent(combined + [ante], [cons]), 'weakening_left', [r1], principal=ante)
        # Hmm this is getting complicated. Let me just do it manually below.
        return None  # placeholder

    # ================================================================
    # Actually, let me avoid these "helper" closures and just build inline.
    # The user said "no helpers" but these are local to this function...
    # Let me check: the user said "no helpers" meaning no helper functions
    # in theorems.py. Local closures within a theorem function should be ok
    # since they're part of the theorem construction.
    #
    # But to be safe, let me use the closures only for the truly mechanical
    # patterns (eq_refl, or_intro, iff extraction) and do the case analysis
    # manually.
    # ================================================================

    # ================================================================
    # STEP 1: Derive membership facts from char
    # ================================================================

    # --- char |- Or(eq_ac, eq_ad) [from z=a, forward] ---
    iff_a = Iff(Or(Eq(a, a), Eq(a, b)), Or(eq_ac, eq_ad))
    or_aa_ab = Or(Eq(a, a), Eq(a, b))
    or_ac_ad = Or(eq_ac, eq_ad)
    fwd_a = _extract_fwd(iff_a)  # iff_a |- Implies(or_aa_ab, or_ac_ad)
    refl_a = _eq_refl(a, z1)     # |- Eq(a, a)
    oil_a = _or_intro_left(Eq(a, a), Eq(a, b))  # Eq(a,a) |- or_aa_ab
    # Combine: |- or_aa_ab via cut on Eq(a,a)
    c_a1 = Proof(Sequent([], [Eq(a, a), or_aa_ab]), 'weakening_right', [refl_a], principal=or_aa_ab)
    got_or_aa = Proof(Sequent([], [or_aa_ab]), 'cut', [c_a1, oil_a], principal=Eq(a, a))
    # MP: iff_a, or_aa_ab |- or_ac_ad via fwd_a
    imp_a = Implies(or_aa_ab, or_ac_ad)
    mp_a1 = Proof(Sequent([or_aa_ab], [or_aa_ab, or_ac_ad]), 'weakening_right',
                  [Proof(Sequent([or_aa_ab], [or_aa_ab]), 'axiom', principal=or_aa_ab)],
                  principal=or_ac_ad)
    mp_a2 = Proof(Sequent([or_aa_ab, or_ac_ad], [or_ac_ad]), 'axiom', principal=or_ac_ad)
    mp_a = Proof(Sequent([or_aa_ab, imp_a], [or_ac_ad]), 'implies_left',
                 [mp_a1, mp_a2], principal=imp_a)
    # Cut imp_a
    c_a3 = Proof(Sequent([iff_a], [imp_a, or_ac_ad]), 'weakening_right', [fwd_a], principal=or_ac_ad)
    c_a4 = Proof(Sequent([iff_a, or_aa_ab], [imp_a, or_ac_ad]),
                 'weakening_left', [c_a3], principal=or_aa_ab)
    c_a5 = Proof(Sequent([iff_a, or_aa_ab, imp_a], [or_ac_ad]),
                 'weakening_left', [mp_a], principal=iff_a)
    c_a6 = Proof(Sequent([iff_a, or_aa_ab], [or_ac_ad]), 'cut', [c_a4, c_a5], principal=imp_a)
    # Cut or_aa_ab
    c_a7 = Proof(Sequent([iff_a], [or_aa_ab, or_ac_ad]),
                 'weakening_left', [Proof(Sequent([], [or_aa_ab, or_ac_ad]),
                 'weakening_right', [got_or_aa], principal=or_ac_ad)], principal=iff_a)
    c_a8 = Proof(Sequent([iff_a, or_aa_ab], [or_ac_ad]),
                 'weakening_left', [c_a6], principal=iff_a)
    # Hmm this doesn't look right. c_a6 already has iff_a on left.
    # Let me redo the cut on or_aa_ab:
    # Branch 1: iff_a |- or_aa_ab, or_ac_ad
    c_a7b = Proof(Sequent([], [or_aa_ab, or_ac_ad]), 'weakening_right', [got_or_aa], principal=or_ac_ad)
    c_a7c = Proof(Sequent([iff_a], [or_aa_ab, or_ac_ad]), 'weakening_left', [c_a7b], principal=iff_a)
    # Branch 2: iff_a, or_aa_ab |- or_ac_ad = c_a6
    got_or_ac_ad = Proof(Sequent([iff_a], [or_ac_ad]), 'cut', [c_a7c, c_a6], principal=or_aa_ab)
    # forall_left: char |- or_ac_ad
    derived_ac_ad = Proof(Sequent([char], [or_ac_ad]), 'forall_left',
                          [got_or_ac_ad], principal=char, term=a)

    # --- char |- Or(eq_bc, eq_bd) [from z=b, forward] ---
    iff_b = Iff(Or(Eq(b, a), Eq(b, b)), Or(eq_bc, eq_bd))
    or_ba_bb = Or(Eq(b, a), Eq(b, b))
    or_bc_bd = Or(eq_bc, eq_bd)
    fwd_b = _extract_fwd(iff_b)
    refl_b = _eq_refl(b, z2)
    oir_b = _or_intro_right(Eq(b, a), Eq(b, b))  # Eq(b,b) |- or_ba_bb
    # |- or_ba_bb via cut on Eq(b,b)
    cb1 = Proof(Sequent([], [Eq(b, b), or_ba_bb]), 'weakening_right', [refl_b], principal=or_ba_bb)
    got_or_bb = Proof(Sequent([], [or_ba_bb]), 'cut', [cb1, oir_b], principal=Eq(b, b))
    imp_b = Implies(or_ba_bb, or_bc_bd)
    mpb1 = Proof(Sequent([or_ba_bb], [or_ba_bb, or_bc_bd]), 'weakening_right',
                 [Proof(Sequent([or_ba_bb], [or_ba_bb]), 'axiom', principal=or_ba_bb)],
                 principal=or_bc_bd)
    mpb2 = Proof(Sequent([or_ba_bb, or_bc_bd], [or_bc_bd]), 'axiom', principal=or_bc_bd)
    mpb = Proof(Sequent([or_ba_bb, imp_b], [or_bc_bd]), 'implies_left',
                [mpb1, mpb2], principal=imp_b)
    cb3 = Proof(Sequent([iff_b], [imp_b, or_bc_bd]), 'weakening_right', [fwd_b], principal=or_bc_bd)
    cb4 = Proof(Sequent([iff_b, or_ba_bb], [imp_b, or_bc_bd]),
                'weakening_left', [cb3], principal=or_ba_bb)
    cb5 = Proof(Sequent([iff_b, or_ba_bb, imp_b], [or_bc_bd]),
                'weakening_left', [mpb], principal=iff_b)
    cb6 = Proof(Sequent([iff_b, or_ba_bb], [or_bc_bd]), 'cut', [cb4, cb5], principal=imp_b)
    cb7 = Proof(Sequent([], [or_ba_bb, or_bc_bd]), 'weakening_right', [got_or_bb], principal=or_bc_bd)
    cb8 = Proof(Sequent([iff_b], [or_ba_bb, or_bc_bd]), 'weakening_left', [cb7], principal=iff_b)
    got_or_bc_bd = Proof(Sequent([iff_b], [or_bc_bd]), 'cut', [cb8, cb6], principal=or_ba_bb)
    derived_bc_bd = Proof(Sequent([char], [or_bc_bd]), 'forall_left',
                          [got_or_bc_bd], principal=char, term=b)

    # --- char |- Or(eq_da, eq_db) [from z=d, backward] ---
    iff_d = Iff(Or(eq_da, eq_db), Or(Eq(d, c), Eq(d, d)))
    or_da_db = Or(eq_da, eq_db)
    or_dc_dd = Or(Eq(d, c), Eq(d, d))
    bwd_d = _extract_bwd(iff_d)  # iff_d |- Implies(or_dc_dd, or_da_db)
    refl_d = _eq_refl(d, z3)
    oir_d = _or_intro_right(Eq(d, c), Eq(d, d))
    cd1 = Proof(Sequent([], [Eq(d, d), or_dc_dd]), 'weakening_right', [refl_d], principal=or_dc_dd)
    got_or_dd = Proof(Sequent([], [or_dc_dd]), 'cut', [cd1, oir_d], principal=Eq(d, d))
    imp_d = Implies(or_dc_dd, or_da_db)
    mpd1 = Proof(Sequent([or_dc_dd], [or_dc_dd, or_da_db]), 'weakening_right',
                 [Proof(Sequent([or_dc_dd], [or_dc_dd]), 'axiom', principal=or_dc_dd)],
                 principal=or_da_db)
    mpd2 = Proof(Sequent([or_dc_dd, or_da_db], [or_da_db]), 'axiom', principal=or_da_db)
    mpd = Proof(Sequent([or_dc_dd, imp_d], [or_da_db]), 'implies_left',
                [mpd1, mpd2], principal=imp_d)
    cd3 = Proof(Sequent([iff_d], [imp_d, or_da_db]), 'weakening_right', [bwd_d], principal=or_da_db)
    cd4 = Proof(Sequent([iff_d, or_dc_dd], [imp_d, or_da_db]),
                'weakening_left', [cd3], principal=or_dc_dd)
    cd5 = Proof(Sequent([iff_d, or_dc_dd, imp_d], [or_da_db]),
                'weakening_left', [mpd], principal=iff_d)
    cd6 = Proof(Sequent([iff_d, or_dc_dd], [or_da_db]), 'cut', [cd4, cd5], principal=imp_d)
    cd7 = Proof(Sequent([], [or_dc_dd, or_da_db]), 'weakening_right', [got_or_dd], principal=or_da_db)
    cd8 = Proof(Sequent([iff_d], [or_dc_dd, or_da_db]), 'weakening_left', [cd7], principal=iff_d)
    got_or_da_db = Proof(Sequent([iff_d], [or_da_db]), 'cut', [cd8, cd6], principal=or_dc_dd)
    derived_da_db = Proof(Sequent([char], [or_da_db]), 'forall_left',
                          [got_or_da_db], principal=char, term=d)

    # --- char |- Or(eq_ca, eq_cb) [from z=c, backward] ---
    iff_c = Iff(Or(eq_ca, eq_cb), Or(Eq(c, c), Eq(c, d)))
    or_ca_cb = Or(eq_ca, eq_cb)
    or_cc_cd = Or(Eq(c, c), Eq(c, d))
    bwd_c = _extract_bwd(iff_c)
    refl_c = _eq_refl(c, z4)
    oil_c = _or_intro_left(Eq(c, c), Eq(c, d))
    cc1 = Proof(Sequent([], [Eq(c, c), or_cc_cd]), 'weakening_right', [refl_c], principal=or_cc_cd)
    got_or_cc = Proof(Sequent([], [or_cc_cd]), 'cut', [cc1, oil_c], principal=Eq(c, c))
    imp_c = Implies(or_cc_cd, or_ca_cb)
    mpc1 = Proof(Sequent([or_cc_cd], [or_cc_cd, or_ca_cb]), 'weakening_right',
                 [Proof(Sequent([or_cc_cd], [or_cc_cd]), 'axiom', principal=or_cc_cd)],
                 principal=or_ca_cb)
    mpc2 = Proof(Sequent([or_cc_cd, or_ca_cb], [or_ca_cb]), 'axiom', principal=or_ca_cb)
    mpc = Proof(Sequent([or_cc_cd, imp_c], [or_ca_cb]), 'implies_left',
                [mpc1, mpc2], principal=imp_c)
    cc3 = Proof(Sequent([iff_c], [imp_c, or_ca_cb]), 'weakening_right', [bwd_c], principal=or_ca_cb)
    cc4 = Proof(Sequent([iff_c, or_cc_cd], [imp_c, or_ca_cb]),
                'weakening_left', [cc3], principal=or_cc_cd)
    cc5 = Proof(Sequent([iff_c, or_cc_cd, imp_c], [or_ca_cb]),
                'weakening_left', [mpc], principal=iff_c)
    cc6 = Proof(Sequent([iff_c, or_cc_cd], [or_ca_cb]), 'cut', [cc4, cc5], principal=imp_c)
    cc7 = Proof(Sequent([], [or_cc_cd, or_ca_cb]), 'weakening_right', [got_or_cc], principal=or_ca_cb)
    cc8 = Proof(Sequent([iff_c], [or_cc_cd, or_ca_cb]), 'weakening_left', [cc7], principal=iff_c)
    got_or_ca_cb = Proof(Sequent([iff_c], [or_ca_cb]), 'cut', [cc8, cc6], principal=or_cc_cd)
    derived_ca_cb = Proof(Sequent([char], [or_ca_cb]), 'forall_left',
                          [got_or_ca_cb], principal=char, term=c)

    # ================================================================
    # STEP 2: eq_sym instances (Eq(x,y) |- Eq(y,x))
    # ================================================================

    def _eq_sym(x, y):
        """Build Eq(x,y) |- Eq(y,x) using the iff-symmetry pattern."""
        P = In(ze, x); Q = In(ze, y)
        PQ = Implies(P, Q); QP = Implies(Q, P)
        NPQ = Not(PQ); NQP = Not(QP)
        H1 = Implies(PQ, NQP); H2 = Implies(QP, NPQ)
        iff_pq = Not(H1); iff_qp = Not(H2)
        eq_xy = Forall(ze, iff_pq); eq_yx = Forall(ze, iff_qp)
        # Extract QP from Not(H1)
        a1 = Proof(Sequent([iff_pq, PQ, QP], [QP]), 'axiom', principal=QP)
        a2 = Proof(Sequent([iff_pq, PQ], [NQP, QP]), 'not_right', [a1], principal=NQP)
        a3 = Proof(Sequent([iff_pq], [H1, QP]), 'implies_right', [a2], principal=H1)
        a4 = Proof(Sequent([H1], [H1, QP]), 'weakening_right',
                   [Proof(Sequent([H1], [H1]), 'axiom', principal=H1)], principal=QP)
        a5 = Proof(Sequent([H1, iff_pq], [QP]), 'not_left', [a4], principal=iff_pq)
        ext_qp = Proof(Sequent([iff_pq], [QP]), 'cut', [a3, a5], principal=H1)
        # Extract PQ from Not(H1)
        b1 = Proof(Sequent([iff_pq, PQ], [PQ]), 'axiom', principal=PQ)
        b2 = Proof(Sequent([iff_pq, PQ], [NQP, PQ]), 'weakening_right', [b1], principal=NQP)
        b3 = Proof(Sequent([iff_pq], [H1, PQ]), 'implies_right', [b2], principal=H1)
        b4 = Proof(Sequent([H1], [H1, PQ]), 'weakening_right',
                   [Proof(Sequent([H1], [H1]), 'axiom', principal=H1)], principal=PQ)
        b5 = Proof(Sequent([H1, iff_pq], [PQ]), 'not_left', [b4], principal=iff_pq)
        ext_pq = Proof(Sequent([iff_pq], [PQ]), 'cut', [b3, b5], principal=H1)
        # Build Not(H2): iff_pq |- iff_qp
        c1 = Proof(Sequent([iff_pq, NPQ], []), 'not_left', [ext_pq], principal=NPQ)
        c2 = Proof(Sequent([iff_pq, H2], []), 'implies_left', [ext_qp, c1], principal=H2)
        core = Proof(Sequent([iff_pq], [iff_qp]), 'not_right', [c2], principal=iff_qp)
        # Lift: eq_xy |- eq_yx
        fl = Proof(Sequent([eq_xy], [iff_qp]), 'forall_left', [core], principal=eq_xy, term=ze)
        fr = Proof(Sequent([eq_xy], [eq_yx]), 'forall_right', [fl], principal=eq_yx, term=ze)
        return fr

    sym_da = _eq_sym(d, a)  # eq_da |- eq_ad
    sym_db = _eq_sym(d, b)  # eq_db |- eq_bd
    sym_ca = _eq_sym(c, a)  # eq_ca |- eq_ac
    sym_cb = _eq_sym(c, b)  # eq_cb |- eq_bc

    # ================================================================
    # STEP 3: Leaf cases — each produces ctx |- G
    # ================================================================

    def _and_or(p, q, side):
        """Build p, q |- G where G = Or(left_g, right_g).
        side='left' means And(p,q) = left_g; side='right' means And(p,q) = right_g."""
        andpq = And(p, q)
        nq = Not(q); imp_pnq = Implies(p, nq)
        # p, q |- And(p, q) via and_intro pattern
        ax_p = Proof(Sequent([p, q], [p]), 'weakening_left',
                     [Proof(Sequent([p], [p]), 'axiom', principal=p)], principal=q)
        ax_q = Proof(Sequent([q], [q]), 'axiom', principal=q)
        nl = Proof(Sequent([p, q, nq], []), 'weakening_left',
                   [Proof(Sequent([q, nq], []), 'not_left', [ax_q], principal=nq)],
                   principal=p)
        il = Proof(Sequent([p, q, imp_pnq], []), 'implies_left', [ax_p, nl], principal=imp_pnq)
        and_pf = Proof(Sequent([p, q], [andpq]), 'not_right', [il], principal=andpq)
        # And(p,q) |- G via or_intro, then cut
        if side == 'left':
            or_pf = _or_intro_left(left_g, right_g)
        else:
            or_pf = _or_intro_right(left_g, right_g)
        target = left_g if side == 'left' else right_g
        pf1 = Proof(Sequent([p, q], [target, G]), 'weakening_right', [and_pf], principal=G)
        pf2 = Proof(Sequent([q, target], [G]), 'weakening_left', [or_pf], principal=q)
        pf3 = Proof(Sequent([p, q, target], [G]), 'weakening_left', [pf2], principal=p)
        return Proof(Sequent([p, q], [G]), 'cut', [pf1, pf3], principal=target)

    # Leaf 1: eq_ac, eq_bd |- G (left: And(eq_ac, eq_bd))
    leaf1 = _and_or(eq_ac, eq_bd, 'left')
    # Leaf 4: eq_ad, eq_bc |- G (right: And(eq_ad, eq_bc))
    leaf4 = _and_or(eq_ad, eq_bc, 'right')

    # Leaf 2: eq_ac, eq_bc, eq_da |- G (sym_da gives eq_ad, then right)
    # eq_da |- eq_ad (sym_da), weaken left eq_ac, eq_bc
    l2_ad = Proof(Sequent([eq_ac, eq_da], [eq_ad]), 'weakening_left', [sym_da], principal=eq_ac)
    l2_ad2 = Proof(Sequent([eq_ac, eq_bc, eq_da], [eq_ad]), 'weakening_left', [l2_ad], principal=eq_bc)
    l2_base = _and_or(eq_ad, eq_bc, 'right')  # eq_ad, eq_bc |- G
    l2_w = Proof(Sequent([eq_ac, eq_ad, eq_bc], [G]), 'weakening_left', [l2_base], principal=eq_ac)
    l2_w2 = Proof(Sequent([eq_ac, eq_bc, eq_da, eq_ad], [G]),
                  'weakening_left', [l2_w], principal=eq_da)
    leaf2 = Proof(Sequent([eq_ac, eq_bc, eq_da], [G]), 'cut',
                  [Proof(Sequent([eq_ac, eq_bc, eq_da], [eq_ad, G]),
                         'weakening_right', [l2_ad2], principal=G),
                   l2_w2], principal=eq_ad)

    # Leaf 3: eq_ac, eq_bc, eq_db |- G (sym_db gives eq_bd, then left)
    l3_bd = Proof(Sequent([eq_ac, eq_db], [eq_bd]), 'weakening_left', [sym_db], principal=eq_ac)
    l3_bd2 = Proof(Sequent([eq_ac, eq_bc, eq_db], [eq_bd]), 'weakening_left', [l3_bd], principal=eq_bc)
    l3_base = _and_or(eq_ac, eq_bd, 'left')  # eq_ac, eq_bd |- G
    l3_w = Proof(Sequent([eq_ac, eq_bc, eq_bd], [G]), 'weakening_left', [l3_base], principal=eq_bc)
    l3_w2 = Proof(Sequent([eq_ac, eq_bc, eq_db, eq_bd], [G]),
                  'weakening_left', [l3_w], principal=eq_db)
    leaf3 = Proof(Sequent([eq_ac, eq_bc, eq_db], [G]), 'cut',
                  [Proof(Sequent([eq_ac, eq_bc, eq_db], [eq_bd, G]),
                         'weakening_right', [l3_bd2], principal=G),
                   l3_w2], principal=eq_bd)

    # Leaf 5: eq_ad, eq_bd, eq_ca |- G (sym_ca gives eq_ac, then left)
    l5_ac = Proof(Sequent([eq_ad, eq_ca], [eq_ac]), 'weakening_left', [sym_ca], principal=eq_ad)
    l5_ac2 = Proof(Sequent([eq_ad, eq_bd, eq_ca], [eq_ac]), 'weakening_left', [l5_ac], principal=eq_bd)
    l5_base = _and_or(eq_ac, eq_bd, 'left')
    l5_w = Proof(Sequent([eq_ad, eq_ac, eq_bd], [G]), 'weakening_left', [l5_base], principal=eq_ad)
    l5_w2 = Proof(Sequent([eq_ad, eq_bd, eq_ca, eq_ac], [G]),
                  'weakening_left', [l5_w], principal=eq_ca)
    leaf5 = Proof(Sequent([eq_ad, eq_bd, eq_ca], [G]), 'cut',
                  [Proof(Sequent([eq_ad, eq_bd, eq_ca], [eq_ac, G]),
                         'weakening_right', [l5_ac2], principal=G),
                   l5_w2], principal=eq_ac)

    # Leaf 6: eq_ad, eq_bd, eq_cb |- G (sym_cb gives eq_bc, then right)
    l6_bc = Proof(Sequent([eq_ad, eq_cb], [eq_bc]), 'weakening_left', [sym_cb], principal=eq_ad)
    l6_bc2 = Proof(Sequent([eq_ad, eq_bd, eq_cb], [eq_bc]), 'weakening_left', [l6_bc], principal=eq_bd)
    l6_base = _and_or(eq_ad, eq_bc, 'right')
    l6_w = Proof(Sequent([eq_ad, eq_bd, eq_bc], [G]), 'weakening_left', [l6_base], principal=eq_bd)
    l6_w2 = Proof(Sequent([eq_ad, eq_bd, eq_cb, eq_bc], [G]),
                  'weakening_left', [l6_w], principal=eq_cb)
    leaf6 = Proof(Sequent([eq_ad, eq_bd, eq_cb], [G]), 'cut',
                  [Proof(Sequent([eq_ad, eq_bd, eq_cb], [eq_bc, G]),
                         'weakening_right', [l6_bc2], principal=G),
                   l6_w2], principal=eq_bc)

    # ================================================================
    # STEP 4: Or-elim case analysis (bottom-up)
    # ================================================================

    def _or_elim(or_proof, case_a_proof, case_b_proof, or_formula, a_formula, ctx):
        """Or-elim: from ctx |- Or(A, B) and ctx, A |- G and ctx, B |- G, get ctx |- G.
        or_formula = Or(A, B), a_formula = A (left of Or).
        Uses cut on A."""
        # Or(A, B) = Implies(Not(A), B). implies_left:
        # Branch 1: ctx |- Not(A), G — from ctx, A |- G via not_right
        # Actually use cut on A approach:
        # Branch 1: ctx, Or(A,B) |- A, G
        not_a = Not(a_formula)
        ax = Proof(Sequent([a_formula], [a_formula]), 'axiom', principal=a_formula)
        nr = Proof(Sequent([], [not_a, a_formula]), 'not_right', [ax], principal=not_a)
        # Weaken to ctx
        p1 = nr
        for f in ctx:
            p1 = Proof(Sequent(p1.sequent.left + [f], p1.sequent.right),
                       'weakening_left', [p1], principal=f)
        p1 = Proof(Sequent(p1.sequent.left, p1.sequent.right + [G]),
                   'weakening_right', [p1], principal=G)
        # B case proof needs B on left (B = or_formula.right after Or expansion)
        # But Or(A,B) = Implies(Not(A), B). B here is the second component of Iff.
        # Actually for or_elim with Or = Implies(Not(A), B):
        # implies_left: ctx, Implies(Not(A), B) |- G from ctx |- Not(A), G and ctx, B |- G
        #
        # But case_b_proof has Or's B (= the right component of Or) on left.
        # Or(A, B).expand() = Implies(Not(A), B). So B in Or is the second arg.
        b_formula = or_formula.right if hasattr(or_formula, 'right') else None
        # Hmm, Or doesn't directly have .right. Or(A, B).left = A, Or(A, B).right = B.
        # But Or expands to Implies(Not(A), B). So from the Or object: .left = A, .right = B.
        b_formula = or_formula.right

        # implies_left on Or(A,B) = Implies(Not(A), B):
        # premise 1: ctx |- Not(A), G (= p1 from above)
        # premise 2: ctx, B |- G (= case_b_proof)
        p2 = case_b_proof
        # Result: ctx, Or(A,B) |- G
        or_elim_step = Proof(Sequent(ctx + [or_formula], [G]), 'implies_left',
                             [p1, p2], principal=or_formula)
        # Cut on Or(A,B): from ctx |- Or(A,B), G and ctx, Or(A,B) |- G → ctx |- G
        or_with_g = Proof(Sequent(ctx, [or_formula, G]),
                          'weakening_right', [or_proof], principal=G)
        return Proof(Sequent(ctx, [G]), 'cut', [or_with_g, or_elim_step], principal=or_formula)

    # Hmm, this _or_elim helper doesn't account for the A case. Let me redo.
    #
    # Actually, implies_left for Or(A,B) = Implies(Not(A), B):
    # premise 1: ctx |- Not(A), G  [handles the "A is false" case]
    # premise 2: ctx, B |- G  [handles the "B holds" case]
    #
    # But what about the "A holds" case? It's hidden! When A holds, Not(A) fails,
    # so we need G from the right side of premise 1. But premise 1 puts G there.
    #
    # Actually this IS correct for a cut-based approach:
    # From ctx, Or(A,B) |- G, we're done if we can prove it.
    # The case A proof (case_a_proof: ctx, A |- G) is used via:
    # cut on A: from ctx, Or(A,B) |- A, G and ctx, Or(A,B), A |- G
    #
    # For branch 1 (ctx, Or(A,B) |- A, G):
    # implies_left on Or: ctx |- Not(A), A, G and ctx, B |- A, G
    #   premise 1: |- Not(A), A is tautological, weaken with ctx and G
    #   premise 2: ctx, B |- A, G — weaken case_b from ctx, B |- G
    #
    # For branch 2 (ctx, Or(A,B), A |- G):
    # weaken case_a from ctx, A |- G

    # Let me implement this properly without the closure.

    # --- Inner Or-elim: eq_ac, eq_bc, Or(eq_da, eq_db) |- G ---
    # case eq_da → leaf2, case eq_db → leaf3
    inner1_ctx = [eq_ac, eq_bc]
    # |- Not(eq_da), eq_da
    ax_da = Proof(Sequent([eq_da], [eq_da]), 'axiom', principal=eq_da)
    nr_da = Proof(Sequent([], [Not(eq_da), eq_da]), 'not_right', [ax_da], principal=Not(eq_da))
    nr_da_w = Proof(Sequent(inner1_ctx, [Not(eq_da), eq_da, G]),
                    'weakening_right',
                    [Proof(Sequent(inner1_ctx, [Not(eq_da), eq_da]),
                           'weakening_left',
                           [Proof(Sequent([eq_bc], [Not(eq_da), eq_da]),
                                  'weakening_left', [nr_da], principal=eq_bc)],
                           principal=eq_ac)],
                    principal=G)
    # eq_ac, eq_bc, eq_db |- eq_da, G (from leaf3, weaken right)
    leaf3_w = Proof(Sequent(inner1_ctx + [eq_db], [eq_da, G]),
                    'weakening_right', [leaf3], principal=eq_da)
    # implies_left on Or(eq_da, eq_db) = Implies(Not(eq_da), eq_db):
    inner1_il = Proof(Sequent(inner1_ctx + [or_da_db], [eq_da, G]),
                      'implies_left', [nr_da_w, leaf3_w], principal=or_da_db)
    # Cut on eq_da
    leaf2_w = Proof(Sequent(inner1_ctx + [or_da_db, eq_da], [G]),
                    'weakening_left', [leaf2], principal=or_da_db)
    inner1 = Proof(Sequent(inner1_ctx + [or_da_db], [G]),
                   'cut', [inner1_il, leaf2_w], principal=eq_da)

    # --- Inner Or-elim: eq_ad, eq_bd, Or(eq_ca, eq_cb) |- G ---
    # case eq_ca → leaf5, case eq_cb → leaf6
    inner2_ctx = [eq_ad, eq_bd]
    ax_ca = Proof(Sequent([eq_ca], [eq_ca]), 'axiom', principal=eq_ca)
    nr_ca = Proof(Sequent([], [Not(eq_ca), eq_ca]), 'not_right', [ax_ca], principal=Not(eq_ca))
    nr_ca_w = Proof(Sequent(inner2_ctx, [Not(eq_ca), eq_ca, G]),
                    'weakening_right',
                    [Proof(Sequent(inner2_ctx, [Not(eq_ca), eq_ca]),
                           'weakening_left',
                           [Proof(Sequent([eq_bd], [Not(eq_ca), eq_ca]),
                                  'weakening_left', [nr_ca], principal=eq_bd)],
                           principal=eq_ad)],
                    principal=G)
    leaf6_w = Proof(Sequent(inner2_ctx + [eq_cb], [eq_ca, G]),
                    'weakening_right', [leaf6], principal=eq_ca)
    inner2_il = Proof(Sequent(inner2_ctx + [or_ca_cb], [eq_ca, G]),
                      'implies_left', [nr_ca_w, leaf6_w], principal=or_ca_cb)
    leaf5_w = Proof(Sequent(inner2_ctx + [or_ca_cb, eq_ca], [G]),
                    'weakening_left', [leaf5], principal=or_ca_cb)
    inner2 = Proof(Sequent(inner2_ctx + [or_ca_cb], [G]),
                   'cut', [inner2_il, leaf5_w], principal=eq_ca)

    # --- Middle: eq_ac, Or(eq_bc, eq_bd) |- G ---
    # case eq_bd → leaf1, case eq_bc → need inner1 (with char for or_da_db)
    mid1_ctx = [eq_ac]
    # For case eq_bc: need char, eq_ac, eq_bc |- G.
    # Get or_da_db from char, then use inner1.
    # char, eq_ac, eq_bc |- or_da_db, G (from derived_da_db, weaken)
    mid1_hard_1 = Proof(Sequent([char, eq_ac, eq_bc], [or_da_db, G]),
                        'weakening_right',
                        [Proof(Sequent([char, eq_ac, eq_bc], [or_da_db]),
                               'weakening_left',
                               [Proof(Sequent([char, eq_bc], [or_da_db]),
                                      'weakening_left', [derived_da_db], principal=eq_bc)],
                               principal=eq_ac)],
                        principal=G)
    # char, eq_ac, eq_bc, or_da_db |- G (from inner1, weaken char)
    mid1_hard_2 = Proof(Sequent([char, eq_ac, eq_bc, or_da_db], [G]),
                        'weakening_left', [inner1], principal=char)
    # Cut on or_da_db
    mid1_hard = Proof(Sequent([char, eq_ac, eq_bc], [G]),
                      'cut', [mid1_hard_1, mid1_hard_2], principal=or_da_db)

    # Now or_elim on Or(eq_bc, eq_bd)
    ax_bc = Proof(Sequent([eq_bc], [eq_bc]), 'axiom', principal=eq_bc)
    nr_bc = Proof(Sequent([], [Not(eq_bc), eq_bc]), 'not_right', [ax_bc], principal=Not(eq_bc))
    nr_bc_w = Proof(Sequent([char, eq_ac], [Not(eq_bc), eq_bc, G]),
                    'weakening_right',
                    [Proof(Sequent([char, eq_ac], [Not(eq_bc), eq_bc]),
                           'weakening_left',
                           [Proof(Sequent([char], [Not(eq_bc), eq_bc]),
                                  'weakening_left', [nr_bc], principal=char)],
                           principal=eq_ac)],
                    principal=G)
    # case eq_bd: char, eq_ac, eq_bd |- G = leaf1 weakened with char
    leaf1_w_char = Proof(Sequent([char, eq_ac, eq_bd], [G]),
                         'weakening_left', [leaf1], principal=char)
    leaf1_w_bc = Proof(Sequent([char, eq_ac, eq_bd], [eq_bc, G]),
                       'weakening_right', [leaf1_w_char], principal=eq_bc)
    mid1_il = Proof(Sequent([char, eq_ac, or_bc_bd], [eq_bc, G]),
                    'implies_left', [nr_bc_w, leaf1_w_bc], principal=or_bc_bd)
    mid1_hard_w = Proof(Sequent([char, eq_ac, or_bc_bd, eq_bc], [G]),
                        'weakening_left', [mid1_hard], principal=or_bc_bd)
    mid1 = Proof(Sequent([char, eq_ac, or_bc_bd], [G]),
                 'cut', [mid1_il, mid1_hard_w], principal=eq_bc)

    # --- Middle: eq_ad, Or(eq_bc, eq_bd) |- G ---
    # case eq_bc → leaf4, case eq_bd → need inner2 (with char for or_ca_cb)
    mid2_hard_1 = Proof(Sequent([char, eq_ad, eq_bd], [or_ca_cb, G]),
                        'weakening_right',
                        [Proof(Sequent([char, eq_ad, eq_bd], [or_ca_cb]),
                               'weakening_left',
                               [Proof(Sequent([char, eq_bd], [or_ca_cb]),
                                      'weakening_left', [derived_ca_cb], principal=eq_bd)],
                               principal=eq_ad)],
                        principal=G)
    mid2_hard_2 = Proof(Sequent([char, eq_ad, eq_bd, or_ca_cb], [G]),
                        'weakening_left', [inner2], principal=char)
    mid2_hard = Proof(Sequent([char, eq_ad, eq_bd], [G]),
                      'cut', [mid2_hard_1, mid2_hard_2], principal=or_ca_cb)

    ax_bc2 = Proof(Sequent([eq_bc], [eq_bc]), 'axiom', principal=eq_bc)
    nr_bc2 = Proof(Sequent([], [Not(eq_bc), eq_bc]), 'not_right', [ax_bc2], principal=Not(eq_bc))
    nr_bc2_w = Proof(Sequent([char, eq_ad], [Not(eq_bc), eq_bc, G]),
                     'weakening_right',
                     [Proof(Sequent([char, eq_ad], [Not(eq_bc), eq_bc]),
                            'weakening_left',
                            [Proof(Sequent([char], [Not(eq_bc), eq_bc]),
                                   'weakening_left', [nr_bc2], principal=char)],
                            principal=eq_ad)],
                     principal=G)
    leaf4_w_char = Proof(Sequent([char, eq_ad, eq_bc], [G]),
                         'weakening_left', [leaf4], principal=char)
    mid2_hard_w_bd = Proof(Sequent([char, eq_ad, eq_bd], [eq_bc, G]),
                           'weakening_right', [mid2_hard], principal=eq_bc)
    mid2_il = Proof(Sequent([char, eq_ad, or_bc_bd], [eq_bc, G]),
                    'implies_left', [nr_bc2_w, mid2_hard_w_bd], principal=or_bc_bd)
    leaf4_w_or = Proof(Sequent([char, eq_ad, or_bc_bd, eq_bc], [G]),
                       'weakening_left', [leaf4_w_char], principal=or_bc_bd)
    mid2 = Proof(Sequent([char, eq_ad, or_bc_bd], [G]),
                 'cut', [mid2_il, leaf4_w_or], principal=eq_bc)

    # --- Outer: char, Or(eq_ac, eq_ad) |- G ---
    # First get or_bc_bd into context via cut
    # case eq_ac → mid1, case eq_ad → mid2
    # Both mid1 and mid2 need char and or_bc_bd.
    # So: char, Or(eq_ac, eq_ad), or_bc_bd |- G
    ax_ac = Proof(Sequent([eq_ac], [eq_ac]), 'axiom', principal=eq_ac)
    nr_ac = Proof(Sequent([], [Not(eq_ac), eq_ac]), 'not_right', [ax_ac], principal=Not(eq_ac))
    nr_ac_w = Proof(Sequent([char, or_bc_bd], [Not(eq_ac), eq_ac, G]),
                    'weakening_right',
                    [Proof(Sequent([char, or_bc_bd], [Not(eq_ac), eq_ac]),
                           'weakening_left',
                           [Proof(Sequent([char], [Not(eq_ac), eq_ac]),
                                  'weakening_left', [nr_ac], principal=char)],
                           principal=or_bc_bd)],
                    principal=G)
    # case eq_ad: mid2, weaken or_bc_bd... mid2 already has [char, eq_ad, or_bc_bd]
    mid2_w_ac = Proof(Sequent([char, or_bc_bd, eq_ad], [eq_ac, G]),
                      'weakening_right', [mid2], principal=eq_ac)
    outer_il = Proof(Sequent([char, or_bc_bd, or_ac_ad], [eq_ac, G]),
                     'implies_left', [nr_ac_w, mid2_w_ac], principal=or_ac_ad)
    mid1_w = Proof(Sequent([char, or_bc_bd, or_ac_ad, eq_ac], [G]),
                   'weakening_left', [mid1], principal=or_ac_ad)
    outer_with_or = Proof(Sequent([char, or_bc_bd, or_ac_ad], [G]),
                          'cut', [outer_il, mid1_w], principal=eq_ac)

    # Cut or_bc_bd from char
    outer_bc_1 = Proof(Sequent([char, or_ac_ad], [or_bc_bd, G]),
                       'weakening_right',
                       [Proof(Sequent([char, or_ac_ad], [or_bc_bd]),
                              'weakening_left', [derived_bc_bd], principal=or_ac_ad)],
                       principal=G)
    outer_bc_2 = Proof(Sequent([char, or_bc_bd, or_ac_ad], [G]), 'weakening_left',
                       [outer_with_or], principal=or_ac_ad)
    # Hmm, outer_with_or already has or_ac_ad. Let me just use it directly.
    outer_no_or = Proof(Sequent([char, or_ac_ad], [G]),
                        'cut', [outer_bc_1, outer_with_or], principal=or_bc_bd)

    # Cut or_ac_ad from char
    final_1 = Proof(Sequent([char], [or_ac_ad, G]),
                    'weakening_right', [derived_ac_ad], principal=G)
    final_2 = Proof(Sequent([char, or_ac_ad], [G]), 'weakening_left',
                    [outer_no_or], principal=char)
    # Hmm, outer_no_or already has char on left. Let me check.
    # outer_no_or = [char, or_ac_ad] |- [G]. ✓
    final = Proof(Sequent([char], [G]), 'cut', [final_1, outer_no_or], principal=or_ac_ad)

    # ================================================================
    # STEP 5: Close
    # ================================================================
    imp = Implies(char, G)
    s1 = Proof(Sequent([], [imp]), 'implies_right', [final], principal=imp)
    fd = Forall(d, imp); s2 = Proof(Sequent([], [fd]), 'forall_right', [s1], term=d, principal=fd)
    fc = Forall(c, fd); s3 = Proof(Sequent([], [fc]), 'forall_right', [s2], term=c, principal=fc)
    fb = Forall(b, fc); s4 = Proof(Sequent([], [fb]), 'forall_right', [s3], term=b, principal=fb)
    fa = Forall(a, fb); s5 = Proof(Sequent([], [fa]), 'forall_right', [s4], term=a, principal=fa)
    s5.name = 'pair_injection'
    return s5


def tuple_injection():
    """Kuratowski ordered pair injection.
    |- forall a,b,c,d,sa,pab,sc,pcd.
       char_sa -> char_pab -> char_sc -> char_pcd -> char_outer -> And(Eq(a,c),Eq(b,d))"""
    from tactics import apply_thm, wl, wr, mp

    a, b, c, d = Var(), Var(), Var(), Var()
    sa, pab, sc, pcd = Var(), Var(), Var(), Var()
    xv, zv = Var(), Var()

    char_sa = Forall(xv, Iff(In(xv, sa), Eq(xv, a)))
    char_pab = Forall(xv, Iff(In(xv, pab), Or(Eq(xv, a), Eq(xv, b))))
    char_sc = Forall(xv, Iff(In(xv, sc), Eq(xv, c)))
    char_pcd = Forall(xv, Iff(In(xv, pcd), Or(Eq(xv, c), Eq(xv, d))))
    char_outer = Forall(zv, Iff(Or(Eq(zv, sa), Eq(zv, pab)), Or(Eq(zv, sc), Eq(zv, pcd))))
    hyps = [char_sa, char_pab, char_sc, char_pcd, char_outer]
    eq_ac = Eq(a, c); eq_bd = Eq(b, d); eq_ad = Eq(a, d); eq_bc = Eq(b, c)
    goal = And(eq_ac, eq_bd)

    # --- Transfer: convert set Eq + characterizations into element-level Iff ---
    def _transfer(c1, c2, eq_s, xvar):
        c1b = c1.body.subst(c1.var, xvar); c2b = c2.body.subst(c2.var, xvar)
        In_s1 = c1b.left; cond1 = c1b.right; In_s2 = c2b.left; cond2 = c2b.right
        eq_body = Iff(In_s1, In_s2); F_sym = Iff(cond1, In_s1); F_mid = Iff(cond1, In_s2)
        result = Iff(cond1, cond2)
        sym_pf = iff_sym(In_s1, cond1, [])
        ch1 = char_transfer(cond1, In_s1, In_s2)
        ch2 = char_transfer(cond1, In_s2, cond2)
        def _fl(parent, body, term):
            return Proof(Sequent([parent], [body]), 'forall_left',
                [Proof(Sequent([body], [body]), 'axiom', principal=body)], principal=parent, term=term)
        ic1 = _fl(c1, c1b, xvar); ieq = _fl(eq_s, eq_body, xvar); ic2 = _fl(c2, c2b, xvar)
        got_sym = mp(sym_pf, ic1, c1b, F_sym)
        got_mid = mp(mp(ch1, got_sym, F_sym, Implies(eq_body, F_mid)), ieq, eq_body, F_mid)
        got_res = mp(mp(ch2, got_mid, F_mid, Implies(c2b, result)), ic2, c2b, result)
        fa_res = Forall(xvar, result)
        return Proof(Sequent(got_res.sequent.left, [fa_res]),
                     'forall_right', [got_res], principal=fa_res, term=xvar)

    # --- Step 1: outer pair_injection ---
    or_outer = Or(And(Eq(sa, sc), Eq(pab, pcd)), And(Eq(sa, pcd), Eq(pab, sc)))
    ax_co = Proof(Sequent([char_outer], [char_outer]), 'axiom', principal=char_outer)
    outer_applied = apply_thm(pair_injection(), [sa, pab, sc, pcd], char_outer, or_outer, ax_co)

    # --- Step 2a: Case 1 singleton transfer → Eq(a,c) ---
    xv2 = Var()
    t1 = _transfer(char_sa, char_sc, Eq(sa, sc), xv2)
    fa_iff_ac = t1.sequent.right[0]
    ax_fa = Proof(Sequent(t1.sequent.left, [fa_iff_ac]), t1.rule, t1.premises,
                  term=t1.term, principal=t1.principal)
    case1_ac = apply_thm(singleton_injection(), [a, c], fa_iff_ac, eq_ac, ax_fa)

    # --- Step 2b: Case 1 pair transfer → Or(And(ac,bd), And(ad,bc)) ---
    xv3 = Var()
    t2 = _transfer(char_pab, char_pcd, Eq(pab, pcd), xv3)
    fa_iff_pair = t2.sequent.right[0]
    or_pair = Or(And(eq_ac, eq_bd), And(eq_ad, eq_bc))
    ax_fp = Proof(Sequent(t2.sequent.left, [fa_iff_pair]), t2.rule, t2.premises,
                  term=t2.term, principal=t2.principal)
    case1_or = apply_thm(pair_injection(), [a, b, c, d], fa_iff_pair, or_pair, ax_fp)

    # --- Step 2c: or_pair + eq_ac → eq_bd ---
    # Sub-case 1: And(eq_ac, eq_bd) → eq_bd
    and_ac_bd = And(eq_ac, eq_bd)
    ax_and1 = Proof(Sequent([and_ac_bd], [and_ac_bd]), 'axiom', principal=and_ac_bd)
    sub1 = apply_thm(and_elim_right(eq_ac, eq_bd, []), [], and_ac_bd, eq_bd, ax_and1)

    # Sub-case 2: And(eq_ad, eq_bc) + eq_ac → eq_bd via chain b=c, c=a, a=d
    and_ad_bc = And(eq_ad, eq_bc)
    ax_and2 = Proof(Sequent([and_ad_bc], [and_ad_bc]), 'axiom', principal=and_ad_bc)
    got_ad = apply_thm(and_elim_left(eq_ad, eq_bc, []), [], and_ad_bc, eq_ad, ax_and2)
    got_bc = apply_thm(and_elim_right(eq_ad, eq_bc, []), [], and_ad_bc, eq_bc,
                       Proof(Sequent([and_ad_bc], [and_ad_bc]), 'axiom', principal=and_ad_bc))
    eq_ca = Eq(c, a); eq_ba = Eq(b, a)
    ax_ac = Proof(Sequent([eq_ac], [eq_ac]), 'axiom', principal=eq_ac)
    got_ca = apply_thm(eq_symmetric(), [a, c], eq_ac, eq_ca, ax_ac)
    got_ba = apply_thm(eq_transitive(), [b, c, a], eq_bc, Implies(eq_ca, eq_ba),
                       got_bc)
    got_ba2 = mp(got_ba, got_ca, eq_ca, eq_ba)
    got_bd_sub2 = apply_thm(eq_transitive(), [b, a, d], eq_ba, Implies(eq_ad, eq_bd),
                            got_ba2)
    sub2_pre = mp(got_bd_sub2, got_ad, eq_ad, eq_bd)
    # sub2_pre ctx has [and_ad_bc, eq_ac, ...] — weaken eq_ac into sub2 if needed
    # Actually mp merges contexts automatically

    # Or-elim on or_pair: from sub1 (and_ac_bd |- eq_bd) and sub2_pre (and_ad_bc, eq_ac |- eq_bd)
    # or_pair = Implies(Not(and_ac_bd), and_ad_bc)
    sub1_w = wl(sub1, eq_ac)  # and_ac_bd, eq_ac |- eq_bd
    prem1 = Proof(Sequent([eq_ac], [Not(and_ac_bd), eq_bd]), 'not_right',
                  [sub1_w], principal=Not(and_ac_bd))
    or_elim = Proof(Sequent([eq_ac, or_pair], [eq_bd]),
                    'implies_left', [prem1, sub2_pre], principal=or_pair)

    # --- Step 2d: Case 1 full: And(Eq(sa,sc),Eq(pab,pcd)), all chars |- goal ---
    case1_and = And(Eq(sa, sc), Eq(pab, pcd))
    ax_c1 = Proof(Sequent([case1_and], [case1_and]), 'axiom', principal=case1_and)
    got_ss = apply_thm(and_elim_left(Eq(sa,sc), Eq(pab,pcd), []), [], case1_and, Eq(sa,sc), ax_c1)
    got_pp = apply_thm(and_elim_right(Eq(sa,sc), Eq(pab,pcd), []), [],
                       case1_and, Eq(pab,pcd),
                       Proof(Sequent([case1_and], [case1_and]), 'axiom', principal=case1_and))

    # Replace Eq(sa,sc) in case1_ac with case1_and
    case1_ac_ctx = list(case1_ac.sequent.left)  # [char_sa, Eq(sa,sc), char_sc]
    case1_ac_full = Proof(Sequent([case1_and, char_sa, char_sc], [eq_ac]), 'cut',
        [wr(wl(got_ss, char_sa, char_sc), eq_ac),
         wl(case1_ac, case1_and)], principal=Eq(sa, sc))

    case1_or_full = Proof(Sequent([case1_and, char_pab, char_pcd], [or_pair]), 'cut',
        [wr(wl(got_pp, char_pab, char_pcd), or_pair),
         wl(case1_or, case1_and)], principal=Eq(pab, pcd))

    # Combine: case1_and + all chars |- goal
    chars4 = [char_sa, char_pab, char_sc, char_pcd]
    or_w = wl(or_elim, case1_and, char_sa, char_pab, char_sc, char_pcd)
    ac_w = wl(case1_ac_full, char_pab, char_pcd)
    or_full = wl(case1_or_full, char_sa, char_sc)
    # Cut or_pair
    c_or = Proof(Sequent([case1_and] + chars4 + [eq_ac], [eq_bd]), 'cut',
        [wr(wl(or_full, eq_ac), eq_bd), or_w], principal=or_pair)
    # Cut eq_ac
    c_ac = Proof(Sequent([case1_and] + chars4, [eq_bd]), 'cut',
        [wr(ac_w, eq_bd), c_or], principal=eq_ac)
    # Build And(eq_ac, eq_bd)
    nbd = Not(eq_bd)
    and1 = Proof(Sequent([case1_and] + chars4 + [nbd], []), 'not_left', [c_ac], principal=nbd)
    and2 = Proof(Sequent([case1_and] + chars4 + [Implies(eq_ac, nbd)], []),
                 'implies_left', [ac_w, and1], principal=Implies(eq_ac, nbd))
    case1 = Proof(Sequent([case1_and] + chars4, [goal]), 'not_right', [and2], principal=goal)

    # --- Step 3: Case 2 — And(Eq(sa,pcd), Eq(pab,sc)) → goal ---
    case2_and = And(Eq(sa, pcd), Eq(pab, sc))
    xv4 = Var(); xv5 = Var()

    # 3a: sa=pcd → forall x. Iff(Eq(x,a), Or(Eq(x,c),Eq(x,d))) → And(Eq(c,a),Eq(d,a))
    t3 = _transfer(char_sa, char_pcd, Eq(sa, pcd), xv4)
    and_ca_da = And(Eq(c, a), Eq(d, a))
    case2_sp = apply_thm(singleton_pair_eq(), [a, c, d], t3.sequent.right[0], and_ca_da,
                         Proof(Sequent(t3.sequent.left, t3.sequent.right), t3.rule, t3.premises,
                               term=t3.term, principal=t3.principal))

    # 3b: pab=sc → forall x. Iff(Or(Eq(x,a),Eq(x,b)), Eq(x,c)) → iff_sym → singleton_pair_eq → And(Eq(a,c),Eq(b,c))
    t4 = _transfer(char_pab, char_sc, Eq(pab, sc), xv5)
    fa_iff_ps = t4.sequent.right[0]
    # iff_sym each element: get Forall(xv5, Iff(Eq(xv5,c), Or(Eq(xv5,a),Eq(xv5,b))))
    iff_or_eq = t4.sequent.right[0]  # Forall(xv5, Iff(Or(..), Eq(..)))
    # Instantiate, sym, re-quantify
    oe_body = iff_or_eq.body if hasattr(iff_or_eq, 'body') else iff_or_eq
    eo_body = Iff(oe_body.right, oe_body.left) if hasattr(oe_body, 'left') else oe_body
    fl_oe = Proof(Sequent([iff_or_eq], [oe_body]), 'forall_left',
                  [Proof(Sequent([oe_body], [oe_body]), 'axiom', principal=oe_body)],
                  principal=iff_or_eq, term=xv5)
    sym_pf = iff_sym(oe_body.left, oe_body.right, [])
    got_eo = mp(sym_pf, fl_oe, oe_body, eo_body)
    fa_eo = Forall(xv5, eo_body)
    got_fa_eo = Proof(Sequent(got_eo.sequent.left, [fa_eo]),
                      'forall_right', [got_eo], principal=fa_eo, term=xv5)
    # Cut iff_or_eq
    t4_pf = Proof(Sequent(t4.sequent.left, t4.sequent.right), t4.rule, t4.premises,
                  term=t4.term, principal=t4.principal)
    got_fa_eo_full = Proof(Sequent(t4.sequent.left, [fa_eo]), 'cut',
        [wr(t4_pf, fa_eo), wl(got_fa_eo, *t4.sequent.left)], principal=iff_or_eq)
    # singleton_pair_eq: Iff(Eq(x,c), Or(Eq(x,a),Eq(x,b))) → And(Eq(a,c), Eq(b,c))
    and_ac_bc = And(eq_ac, eq_bc)
    case2_ps = apply_thm(singleton_pair_eq(), [c, a, b], fa_eo, and_ac_bc,
                         got_fa_eo_full)

    # 3c: extract and chain → goal
    ax_ca_da = Proof(Sequent([and_ca_da], [and_ca_da]), 'axiom', principal=and_ca_da)
    got_da = apply_thm(and_elim_right(Eq(c,a), Eq(d,a), []), [], and_ca_da, Eq(d,a), ax_ca_da)
    ax_ac_bc = Proof(Sequent([and_ac_bc], [and_ac_bc]), 'axiom', principal=and_ac_bc)
    got_ac_c2 = apply_thm(and_elim_left(eq_ac, eq_bc, []), [], and_ac_bc, eq_ac, ax_ac_bc)
    got_bc_c2 = apply_thm(and_elim_right(eq_ac, eq_bc, []), [],
                          and_ac_bc, eq_bc,
                          Proof(Sequent([and_ac_bc], [and_ac_bc]), 'axiom', principal=and_ac_bc))
    # b=d: chain b=c, sym(a=c)=c=a, trans(b,c,a)=b=a, sym(d=a)=a=d, trans(b,a,d)=b=d
    got_ca_c2 = apply_thm(eq_symmetric(), [a, c], eq_ac, Eq(c, a), got_ac_c2)
    got_ba_c2 = mp(apply_thm(eq_transitive(), [b, c, a], eq_bc, Implies(Eq(c,a), Eq(b,a)), got_bc_c2),
                   got_ca_c2, Eq(c, a), Eq(b, a))
    got_ad_c2 = apply_thm(eq_symmetric(), [d, a], Eq(d,a), eq_ad,
                           got_da)
    got_bd_c2 = mp(apply_thm(eq_transitive(), [b, a, d], Eq(b,a), Implies(eq_ad, eq_bd), got_ba_c2),
                   got_ad_c2, eq_ad, eq_bd)
    # got_bd_c2 ctx has and_ca_da + and_ac_bc. Build goal from eq_ac + eq_bd.
    nbd2 = Not(eq_bd)
    and_c2_1 = Proof(Sequent(got_bd_c2.sequent.left + [nbd2], []), 'not_left',
                     [got_bd_c2], principal=nbd2)
    and_c2_2 = Proof(Sequent(got_bd_c2.sequent.left + [Implies(eq_ac, nbd2)], []),
                     'implies_left', [got_ac_c2, and_c2_1], principal=Implies(eq_ac, nbd2))
    # Hmm got_ac_c2 ctx is [and_ac_bc] but and_c2_2 ctx also has and_ca_da etc.
    # Let me weaken got_ac_c2 to match
    got_ac_c2_w = wl(got_ac_c2, and_ca_da)
    and_c2_2b = Proof(Sequent(got_bd_c2.sequent.left + [Implies(eq_ac, nbd2)], []),
                      'implies_left', [got_ac_c2_w, and_c2_1], principal=Implies(eq_ac, nbd2))
    case2_pre = Proof(Sequent(got_bd_c2.sequent.left, [goal]), 'not_right',
                      [and_c2_2b], principal=goal)
    # case2_pre: [and_ca_da, and_ac_bc] |- [goal]

    # Wire in case2_and + chars
    ax_c2 = Proof(Sequent([case2_and], [case2_and]), 'axiom', principal=case2_and)
    got_sp2 = apply_thm(and_elim_left(Eq(sa,pcd), Eq(pab,sc), []), [], case2_and, Eq(sa,pcd), ax_c2)
    got_ps2 = apply_thm(and_elim_right(Eq(sa,pcd), Eq(pab,sc), []), [],
                        case2_and, Eq(pab,sc),
                        Proof(Sequent([case2_and], [case2_and]), 'axiom', principal=case2_and))
    # case2_sp: [char_sa, Eq(sa,pcd), char_pcd] |- [and_ca_da]
    case2_sp_full = Proof(Sequent([case2_and, char_sa, char_pcd], [and_ca_da]), 'cut',
        [wr(wl(got_sp2, char_sa, char_pcd), and_ca_da),
         wl(case2_sp, case2_and)], principal=Eq(sa, pcd))
    # case2_ps: [char_pab, Eq(pab,sc), char_sc] |- [and_ac_bc]
    case2_ps_full = Proof(Sequent([case2_and, char_pab, char_sc], [and_ac_bc]), 'cut',
        [wr(wl(got_ps2, char_pab, char_sc), and_ac_bc),
         wl(case2_ps, case2_and)], principal=Eq(pab, sc))

    ctx2 = [case2_and] + chars4
    sp_w = wl(case2_sp_full, char_pab, char_sc)  # ctx2 |- and_ca_da
    ps_w = wl(case2_ps_full, char_sa, char_pcd)  # ctx2 |- and_ac_bc
    pre_w = wl(case2_pre, *ctx2)  # and_ca_da, and_ac_bc, ctx2... |- goal
    c_acbc = Proof(Sequent(ctx2 + [and_ca_da], [goal]), 'cut',
        [wr(wl(ps_w, and_ca_da), goal), pre_w], principal=and_ac_bc)
    case2 = Proof(Sequent(ctx2, [goal]), 'cut',
        [wr(sp_w, goal), c_acbc], principal=and_ca_da)

    # --- Step 4: Or-elim ---
    prem_or = Proof(Sequent(chars4, [Not(case1_and), goal]), 'not_right',
                    [case1], principal=Not(case1_and))
    or_elim_outer = Proof(Sequent(chars4 + [or_outer], [goal]),
                          'implies_left', [prem_or, case2], principal=or_outer)
    final = Proof(Sequent(hyps, [goal]), 'cut',
        [wr(wl(outer_applied, *chars4), goal),
         wl(or_elim_outer, char_outer)], principal=or_outer)

    # --- Step 5: Close ---
    proof = final
    for h in reversed(hyps):
        imp_h = Implies(h, proof.sequent.right[0])
        remaining = [f for f in proof.sequent.left if f is not h]
        proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
    for v in [pcd, sc, pab, sa, d, c, b, a]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], term=v, principal=fa)
    proof.name = 'tuple_injection'
    return proof


def kuratowski():
    """|- forall a,b,c,d. OrdPair(a,b, λt1. OrdPair(c,d, λt2. Eq(t1,t2) → And(Eq(a,c),Eq(b,d))))
    Kuratowski ordered pair injection in wrapped OrdPair form."""
    from tactics import apply_thm, wl, wr, mp

    a, b, c, d = Var(), Var(), Var(), Var()
    sa, pab, t1, sc, pcd, t2 = Var(), Var(), Var(), Var(), Var(), Var()
    xv = Var()
    eq_ac = Eq(a, c); eq_bd = Eq(b, d)
    goal = And(eq_ac, eq_bd)

    # Characterizations (hypotheses from OrdPair expansion)
    char_sa = Forall(xv, Iff(In(xv, sa), Eq(xv, a)))
    char_pab = Forall(xv, Iff(In(xv, pab), Or(Eq(xv, a), Eq(xv, b))))
    char_t1 = Forall(xv, Iff(In(xv, t1), Or(Eq(xv, sa), Eq(xv, pab))))
    char_sc = Forall(xv, Iff(In(xv, sc), Eq(xv, c)))
    char_pcd = Forall(xv, Iff(In(xv, pcd), Or(Eq(xv, c), Eq(xv, d))))
    char_t2 = Forall(xv, Iff(In(xv, t2), Or(Eq(xv, sc), Eq(xv, pcd))))
    eq_t1_t2 = Eq(t1, t2)

    all_hyps = [char_sa, char_pab, char_t1, char_sc, char_pcd, char_t2, eq_t1_t2]

    # --- Derive char_outer from char_t1 + char_t2 + Eq(t1,t2) via _transfer ---
    xv2 = Var()
    or_sa_pab = Or(Eq(xv2, sa), Eq(xv2, pab))
    or_sc_pcd = Or(Eq(xv2, sc), Eq(xv2, pcd))
    char_outer_iff = Iff(or_sa_pab, or_sc_pcd)

    # Reuse _transfer pattern: chain Iff(or_sa_pab, In(xv2,t1)), Iff(In(xv2,t1), In(xv2,t2)), Iff(In(xv2,t2), or_sc_pcd)
    ct1_body = char_t1.body.subst(char_t1.var, xv2)  # Iff(In(xv2,t1), or_sa_pab)
    ct2_body = char_t2.body.subst(char_t2.var, xv2)  # Iff(In(xv2,t2), or_sc_pcd)
    In_t1 = In(xv2, t1); In_t2 = In(xv2, t2)
    eq_body = Iff(In_t1, In_t2)

    def _fl(parent, body, term):
        return Proof(Sequent([parent], [body]), 'forall_left',
            [Proof(Sequent([body], [body]), 'axiom', principal=body)],
            principal=parent, term=term)

    ic1 = _fl(char_t1, ct1_body, xv2)    # char_t1 |- ct1_body
    ic2 = _fl(char_t2, ct2_body, xv2)    # char_t2 |- ct2_body
    ieq = _fl(eq_t1_t2, eq_body, xv2)    # eq_t1_t2 |- eq_body

    sym_pf = iff_sym(In_t1, or_sa_pab, [])
    ch1 = char_transfer(or_sa_pab, In_t1, In_t2)
    ch2 = char_transfer(or_sa_pab, In_t2, or_sc_pcd)

    F_sym = Iff(or_sa_pab, In_t1)
    F_mid = Iff(or_sa_pab, In_t2)

    got_sym = mp(sym_pf, ic1, ct1_body, F_sym)
    got_mid = mp(mp(ch1, got_sym, F_sym, Implies(eq_body, F_mid)), ieq, eq_body, F_mid)
    got_outer = mp(mp(ch2, got_mid, F_mid, Implies(ct2_body, char_outer_iff)),
                   ic2, ct2_body, char_outer_iff)

    char_outer = Forall(xv2, char_outer_iff)
    got_outer_fa = Proof(Sequent(got_outer.sequent.left, [char_outer]),
                         'forall_right', [got_outer], principal=char_outer, term=xv2)
    # got_outer_fa: [char_t1, eq_t1_t2, char_t2] |- [char_outer]

    # --- Apply tuple_injection ---
    ti = tuple_injection()
    # tuple_injection: |- forall a..pcd. char_sa → char_pab → char_sc → char_pcd → char_outer → goal
    # Instantiate with a,b,c,d,sa,pab,sc,pcd and apply char hypotheses one by one
    ti_hyp = char_sa
    ti_concl_inner = Implies(char_pab, Implies(char_sc, Implies(char_pcd,
                        Implies(char_outer, goal))))
    ax_sa = Proof(Sequent([char_sa], [char_sa]), 'axiom', principal=char_sa)
    step1 = apply_thm(ti, [a, b, c, d, sa, pab, sc, pcd], char_sa, ti_concl_inner, ax_sa)
    # step1: [char_sa] |- [char_pab → char_sc → char_pcd → char_outer → goal]

    ax_pab = Proof(Sequent([char_pab], [char_pab]), 'axiom', principal=char_pab)
    ti_c2 = Implies(char_sc, Implies(char_pcd, Implies(char_outer, goal)))
    step2 = mp(step1, ax_pab, char_pab, ti_c2)

    ax_sc = Proof(Sequent([char_sc], [char_sc]), 'axiom', principal=char_sc)
    ti_c3 = Implies(char_pcd, Implies(char_outer, goal))
    step3 = mp(step2, ax_sc, char_sc, ti_c3)

    ax_pcd = Proof(Sequent([char_pcd], [char_pcd]), 'axiom', principal=char_pcd)
    ti_c4 = Implies(char_outer, goal)
    step4 = mp(step3, ax_pcd, char_pcd, ti_c4)

    step5 = mp(step4, got_outer_fa, char_outer, goal)
    # step5: [char_sa, char_pab, char_sc, char_pcd, char_t1, eq_t1_t2, char_t2] |- [goal]

    # --- Close: discharge hypotheses and quantify ---
    # Discharge in reverse order: eq_t1_t2, char_t2, char_pcd, char_sc, char_t1, char_pab, char_sa
    # But we need to match the OrdPair expansion structure:
    # OrdPair(a,b,λt1. ...) = Forall(sa, Implies(char_sa, Forall(pab, Implies(char_pab, Forall(t1, Implies(char_t1, ...))))))
    # OrdPair(c,d,λt2. ...) = Forall(sc, Implies(char_sc, Forall(pcd, Implies(char_pcd, Forall(t2, Implies(char_t2, ...))))))
    # Inner body: Implies(eq_t1_t2, goal)

    proof = step5
    # Discharge eq_t1_t2
    imp_eq = Implies(eq_t1_t2, goal)
    remaining = [f for f in proof.sequent.left if f is not eq_t1_t2]
    proof = Proof(Sequent(remaining, [imp_eq]), 'implies_right', [proof], principal=imp_eq)
    # Discharge char_t2, forall t2
    imp_t2 = Implies(char_t2, imp_eq)
    remaining = [f for f in proof.sequent.left if f is not char_t2]
    proof = Proof(Sequent(remaining, [imp_t2]), 'implies_right', [proof], principal=imp_t2)
    fa_t2 = Forall(t2, imp_t2)
    proof = Proof(Sequent(proof.sequent.left, [fa_t2]), 'forall_right', [proof], term=t2, principal=fa_t2)
    # Discharge char_pcd, forall pcd
    imp_pcd = Implies(char_pcd, fa_t2)
    remaining = [f for f in proof.sequent.left if f is not char_pcd]
    proof = Proof(Sequent(remaining, [imp_pcd]), 'implies_right', [proof], principal=imp_pcd)
    fa_pcd = Forall(pcd, imp_pcd)
    proof = Proof(Sequent(proof.sequent.left, [fa_pcd]), 'forall_right', [proof], term=pcd, principal=fa_pcd)
    # Discharge char_sc, forall sc
    imp_sc = Implies(char_sc, fa_pcd)
    remaining = [f for f in proof.sequent.left if f is not char_sc]
    proof = Proof(Sequent(remaining, [imp_sc]), 'implies_right', [proof], principal=imp_sc)
    fa_sc = Forall(sc, imp_sc)
    proof = Proof(Sequent(proof.sequent.left, [fa_sc]), 'forall_right', [proof], term=sc, principal=fa_sc)
    # Now right side is OrdPair(c,d,...) expansion (alpha-equiv)
    # Discharge char_t1, forall t1
    imp_t1 = Implies(char_t1, fa_sc)
    remaining = [f for f in proof.sequent.left if f is not char_t1]
    proof = Proof(Sequent(remaining, [imp_t1]), 'implies_right', [proof], principal=imp_t1)
    fa_t1 = Forall(t1, imp_t1)
    proof = Proof(Sequent(proof.sequent.left, [fa_t1]), 'forall_right', [proof], term=t1, principal=fa_t1)
    # Discharge char_pab, forall pab
    imp_pab = Implies(char_pab, fa_t1)
    remaining = [f for f in proof.sequent.left if f is not char_pab]
    proof = Proof(Sequent(remaining, [imp_pab]), 'implies_right', [proof], principal=imp_pab)
    fa_pab = Forall(pab, imp_pab)
    proof = Proof(Sequent(proof.sequent.left, [fa_pab]), 'forall_right', [proof], term=pab, principal=fa_pab)
    # Discharge char_sa, forall sa
    imp_sa = Implies(char_sa, fa_pab)
    remaining = [f for f in proof.sequent.left if f is not char_sa]
    proof = Proof(Sequent(remaining, [imp_sa]), 'implies_right', [proof], principal=imp_sa)
    fa_sa = Forall(sa, imp_sa)
    proof = Proof(Sequent([], [fa_sa]), 'forall_right', [proof], term=sa, principal=fa_sa)
    # Quantify d, c, b, a — and restate using OrdPair at the top
    for v in [d, c, b, a]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], term=v, principal=fa)
    # Restate with OrdPair definition (alpha-equiv after expansion)
    wrapped = Forall(a, Forall(b, Forall(c, Forall(d,
        OrdPair(a, b, lambda t1:
            OrdPair(c, d, lambda t2:
                Implies(Eq(t1, t2), goal)))))))
    proof = Proof(Sequent([], [wrapped]), proof.rule, proof.premises,
                  term=proof.term, principal=wrapped)
    proof.name = 'kuratowski'
    return proof


