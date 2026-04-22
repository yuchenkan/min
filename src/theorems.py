"""Theorems proved from the sequent calculus. All theorems are closed (no free vars)."""

from core.lang import Var, In, Not, Implies, Forall
from core.derived import Eq, Iff, And, Or, Exists
from core.proof import Sequent, Proof
from core import zfc
from definitions import EmptySet


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


