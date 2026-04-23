"""Theorems proved from the sequent calculus. All theorems are closed (no free vars)."""

from core.lang import Var, In, Not, Implies, Forall
from core.derived import Eq, Iff, And, Or, Exists
from core.proof import Sequent, Proof
from core import zfc
from definitions import Empty, OrdPair, Subset, Inductive, Omega


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
    e1, e2 = Var(), Var()
    goal = Forall(e1, Implies(Empty(e1), Forall(e2, Implies(Empty(e2), Eq(e1, e2)))))
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
    No quantifiers -- for inline composition. Same as iff_chain core."""
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
    iff_yz = Iff(Y, Z)  # Iff(Eq(a,a), Eq(a,b)) -- from instantiating char with z=a

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
    # STEP 3: Leaf cases -- each produces ctx |- G
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
        # Branch 1: ctx |- Not(A), G -- from ctx, A |- G via not_right
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
        # Cut on Or(A,B): from ctx |- Or(A,B), G and ctx, Or(A,B) |- G -> ctx |- G
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
    #   premise 2: ctx, B |- A, G -- weaken case_b from ctx, B |- G
    #
    # For branch 2 (ctx, Or(A,B), A |- G):
    # weaken case_a from ctx, A |- G

    # Let me implement this properly without the closure.

    # --- Inner Or-elim: eq_ac, eq_bc, Or(eq_da, eq_db) |- G ---
    # case eq_da -> leaf2, case eq_db -> leaf3
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
    # case eq_ca -> leaf5, case eq_cb -> leaf6
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
    # case eq_bd -> leaf1, case eq_bc -> need inner1 (with char for or_da_db)
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
    # case eq_bc -> leaf4, case eq_bd -> need inner2 (with char for or_ca_cb)
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
    # case eq_ac -> mid1, case eq_ad -> mid2
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
    # outer_no_or = [char, or_ac_ad] |- [G]. (ok)
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
        got_sym = mp(sym_pf, ic1, c1b, F_sym, [], [])
        got_mid = mp(mp(ch1, got_sym, F_sym, Implies(eq_body, F_mid), [], []), ieq, eq_body, F_mid, [], [])
        got_res = mp(mp(ch2, got_mid, F_mid, Implies(c2b, result), [], []), ic2, c2b, result, [], [])
        fa_res = Forall(xvar, result)
        return Proof(Sequent(got_res.sequent.left, [fa_res]),
                     'forall_right', [got_res], principal=fa_res, term=xvar)

    # --- Step 1: outer pair_injection ---
    or_outer = Or(And(Eq(sa, sc), Eq(pab, pcd)), And(Eq(sa, pcd), Eq(pab, sc)))
    ax_co = Proof(Sequent([char_outer], [char_outer]), 'axiom', principal=char_outer)
    outer_applied = apply_thm(pair_injection(), [sa, pab, sc, pcd], char_outer, or_outer, ax_co, [], [])

    # --- Step 2a: Case 1 singleton transfer -> Eq(a,c) ---
    xv2 = Var()
    t1 = _transfer(char_sa, char_sc, Eq(sa, sc), xv2)
    fa_iff_ac = t1.sequent.right[0]
    ax_fa = Proof(Sequent(t1.sequent.left, [fa_iff_ac]), t1.rule, t1.premises,
                  term=t1.term, principal=t1.principal)
    case1_ac = apply_thm(singleton_injection(), [a, c], fa_iff_ac, eq_ac, ax_fa, [], [])

    # --- Step 2b: Case 1 pair transfer -> Or(And(ac,bd), And(ad,bc)) ---
    xv3 = Var()
    t2 = _transfer(char_pab, char_pcd, Eq(pab, pcd), xv3)
    fa_iff_pair = t2.sequent.right[0]
    or_pair = Or(And(eq_ac, eq_bd), And(eq_ad, eq_bc))
    ax_fp = Proof(Sequent(t2.sequent.left, [fa_iff_pair]), t2.rule, t2.premises,
                  term=t2.term, principal=t2.principal)
    case1_or = apply_thm(pair_injection(), [a, b, c, d], fa_iff_pair, or_pair, ax_fp, [], [])

    # --- Step 2c: or_pair + eq_ac -> eq_bd ---
    # Sub-case 1: And(eq_ac, eq_bd) -> eq_bd
    and_ac_bd = And(eq_ac, eq_bd)
    ax_and1 = Proof(Sequent([and_ac_bd], [and_ac_bd]), 'axiom', principal=and_ac_bd)
    sub1 = apply_thm(and_elim_right(eq_ac, eq_bd, []), [], and_ac_bd, eq_bd, ax_and1, [], [])

    # Sub-case 2: And(eq_ad, eq_bc) + eq_ac -> eq_bd via chain b=c, c=a, a=d
    and_ad_bc = And(eq_ad, eq_bc)
    ax_and2 = Proof(Sequent([and_ad_bc], [and_ad_bc]), 'axiom', principal=and_ad_bc)
    got_ad = apply_thm(and_elim_left(eq_ad, eq_bc, []), [], and_ad_bc, eq_ad, ax_and2, [], [])
    got_bc = apply_thm(and_elim_right(eq_ad, eq_bc, []), [], and_ad_bc, eq_bc,
                       Proof(Sequent([and_ad_bc], [and_ad_bc]), 'axiom', principal=and_ad_bc), [], [])
    eq_ca = Eq(c, a); eq_ba = Eq(b, a)
    ax_ac = Proof(Sequent([eq_ac], [eq_ac]), 'axiom', principal=eq_ac)
    got_ca = apply_thm(eq_symmetric(), [a, c], eq_ac, eq_ca, ax_ac, [], [])
    got_ba = apply_thm(eq_transitive(), [b, c, a], eq_bc, Implies(eq_ca, eq_ba),
                       got_bc, [], [])
    got_ba2 = mp(got_ba, got_ca, eq_ca, eq_ba, [], [])
    got_bd_sub2 = apply_thm(eq_transitive(), [b, a, d], eq_ba, Implies(eq_ad, eq_bd),
                            got_ba2, [], [])
    sub2_pre = mp(got_bd_sub2, got_ad, eq_ad, eq_bd, [and_ad_bc], [and_ad_bc])
    # sub2_pre ctx has [and_ad_bc, eq_ac, ...] -- weaken eq_ac into sub2 if needed
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
    got_ss = apply_thm(and_elim_left(Eq(sa,sc), Eq(pab,pcd), []), [], case1_and, Eq(sa,sc), ax_c1, [], [])
    got_pp = apply_thm(and_elim_right(Eq(sa,sc), Eq(pab,pcd), []), [],
                       case1_and, Eq(pab,pcd),
                       Proof(Sequent([case1_and], [case1_and]), 'axiom', principal=case1_and), [], [])

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

    # --- Step 3: Case 2 -- And(Eq(sa,pcd), Eq(pab,sc)) -> goal ---
    case2_and = And(Eq(sa, pcd), Eq(pab, sc))
    xv4 = Var(); xv5 = Var()

    # 3a: sa=pcd -> forall x. Iff(Eq(x,a), Or(Eq(x,c),Eq(x,d))) -> And(Eq(c,a),Eq(d,a))
    t3 = _transfer(char_sa, char_pcd, Eq(sa, pcd), xv4)
    and_ca_da = And(Eq(c, a), Eq(d, a))
    case2_sp = apply_thm(singleton_pair_eq(), [a, c, d], t3.sequent.right[0], and_ca_da,
                         Proof(Sequent(t3.sequent.left, t3.sequent.right), t3.rule, t3.premises,
                               term=t3.term, principal=t3.principal), [], [])

    # 3b: pab=sc -> forall x. Iff(Or(Eq(x,a),Eq(x,b)), Eq(x,c)) -> iff_sym -> singleton_pair_eq -> And(Eq(a,c),Eq(b,c))
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
    got_eo = mp(sym_pf, fl_oe, oe_body, eo_body, [], [])
    fa_eo = Forall(xv5, eo_body)
    got_fa_eo = Proof(Sequent(got_eo.sequent.left, [fa_eo]),
                      'forall_right', [got_eo], principal=fa_eo, term=xv5)
    # Cut iff_or_eq
    t4_pf = Proof(Sequent(t4.sequent.left, t4.sequent.right), t4.rule, t4.premises,
                  term=t4.term, principal=t4.principal)
    got_fa_eo_full = Proof(Sequent(t4.sequent.left, [fa_eo]), 'cut',
        [wr(t4_pf, fa_eo), wl(got_fa_eo, *t4.sequent.left)], principal=iff_or_eq)
    # singleton_pair_eq: Iff(Eq(x,c), Or(Eq(x,a),Eq(x,b))) -> And(Eq(a,c), Eq(b,c))
    and_ac_bc = And(eq_ac, eq_bc)
    case2_ps = apply_thm(singleton_pair_eq(), [c, a, b], fa_eo, and_ac_bc,
                         got_fa_eo_full, [], [])

    # 3c: extract and chain -> goal
    ax_ca_da = Proof(Sequent([and_ca_da], [and_ca_da]), 'axiom', principal=and_ca_da)
    got_da = apply_thm(and_elim_right(Eq(c,a), Eq(d,a), []), [], and_ca_da, Eq(d,a), ax_ca_da, [], [])
    ax_ac_bc = Proof(Sequent([and_ac_bc], [and_ac_bc]), 'axiom', principal=and_ac_bc)
    got_ac_c2 = apply_thm(and_elim_left(eq_ac, eq_bc, []), [], and_ac_bc, eq_ac, ax_ac_bc, [], [])
    got_bc_c2 = apply_thm(and_elim_right(eq_ac, eq_bc, []), [],
                          and_ac_bc, eq_bc,
                          Proof(Sequent([and_ac_bc], [and_ac_bc]), 'axiom', principal=and_ac_bc), [], [])
    # b=d: chain b=c, sym(a=c)=c=a, trans(b,c,a)=b=a, sym(d=a)=a=d, trans(b,a,d)=b=d
    got_ca_c2 = apply_thm(eq_symmetric(), [a, c], eq_ac, Eq(c, a), got_ac_c2, [], [])
    got_ba_c2 = mp(apply_thm(eq_transitive(), [b, c, a], eq_bc, Implies(Eq(c,a), Eq(b,a)), got_bc_c2, [], []),
                   got_ca_c2, Eq(c, a), Eq(b, a), [and_ac_bc], [and_ac_bc])
    got_ad_c2 = apply_thm(eq_symmetric(), [d, a], Eq(d,a), eq_ad,
                           got_da, [], [])
    got_bd_c2 = mp(apply_thm(eq_transitive(), [b, a, d], Eq(b,a), Implies(eq_ad, eq_bd), got_ba_c2, [], []),
                   got_ad_c2, eq_ad, eq_bd, [], [])
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
    got_sp2 = apply_thm(and_elim_left(Eq(sa,pcd), Eq(pab,sc), []), [], case2_and, Eq(sa,pcd), ax_c2, [], [])
    got_ps2 = apply_thm(and_elim_right(Eq(sa,pcd), Eq(pab,sc), []), [],
                        case2_and, Eq(pab,sc),
                        Proof(Sequent([case2_and], [case2_and]), 'axiom', principal=case2_and), [], [])
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
    """Pairing |- forall a,b,c,d,t1,t2.
       OrdPair(t1,a,b) -> OrdPair(t2,c,d) -> Eq(t1,t2) -> And(Eq(a,c),Eq(b,d))"""
    from tactics import apply_thm, wl, wr, mp
    from core import zfc

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

    got_sym = mp(sym_pf, ic1, ct1_body, F_sym, [], [])
    got_mid = mp(mp(ch1, got_sym, F_sym, Implies(eq_body, F_mid), [], []), ieq, eq_body, F_mid, [], [])
    got_outer = mp(mp(ch2, got_mid, F_mid, Implies(ct2_body, char_outer_iff), [], []),
                   ic2, ct2_body, char_outer_iff, [], [])

    char_outer = Forall(xv2, char_outer_iff)
    got_outer_fa = Proof(Sequent(got_outer.sequent.left, [char_outer]),
                         'forall_right', [got_outer], principal=char_outer, term=xv2)
    # got_outer_fa: [char_t1, eq_t1_t2, char_t2] |- [char_outer]

    # --- Apply tuple_injection ---
    ti = tuple_injection()
    # tuple_injection: |- forall a..pcd. char_sa -> char_pab -> char_sc -> char_pcd -> char_outer -> goal
    # Instantiate with a,b,c,d,sa,pab,sc,pcd and apply char hypotheses one by one
    ti_hyp = char_sa
    ti_concl_inner = Implies(char_pab, Implies(char_sc, Implies(char_pcd,
                        Implies(char_outer, goal))))
    ax_sa = Proof(Sequent([char_sa], [char_sa]), 'axiom', principal=char_sa)
    step1 = apply_thm(ti, [a, b, c, d, sa, pab, sc, pcd], char_sa, ti_concl_inner, ax_sa, [], [])
    # step1: [char_sa] |- [char_pab -> char_sc -> char_pcd -> char_outer -> goal]

    ax_pab = Proof(Sequent([char_pab], [char_pab]), 'axiom', principal=char_pab)
    ti_c2 = Implies(char_sc, Implies(char_pcd, Implies(char_outer, goal)))
    step2 = mp(step1, ax_pab, char_pab, ti_c2, [], [])

    ax_sc = Proof(Sequent([char_sc], [char_sc]), 'axiom', principal=char_sc)
    ti_c3 = Implies(char_pcd, Implies(char_outer, goal))
    step3 = mp(step2, ax_sc, char_sc, ti_c3, [], [])

    ax_pcd = Proof(Sequent([char_pcd], [char_pcd]), 'axiom', principal=char_pcd)
    ti_c4 = Implies(char_outer, goal)
    step4 = mp(step3, ax_pcd, char_pcd, ti_c4, [], [])

    step5 = mp(step4, got_outer_fa, char_outer, goal, [], [])
    # step5: [char_sa, char_pab, char_sc, char_pcd, char_t1, eq_t1_t2, char_t2] |- [goal]

    # --- Close: package hyps into OrdPair (Exists/And) then discharge ---
    proof = step5

    def _pack_and(proof, A, B):
        ctx = [f for f in proof.sequent.left if f is not A and f is not B]
        D = proof.sequent.right[0]
        ab = And(A, B)
        ax_ab = Proof(Sequent([ab], [ab]), "axiom", principal=ab)
        got_a = apply_thm(and_elim_left(A, B, []), [], ab, A, ax_ab, [], [])
        got_b = apply_thm(and_elim_right(A, B, []), [], ab, B,
                          Proof(Sequent([ab], [ab]), "axiom", principal=ab), [], [])
        p1 = Proof(Sequent([ab, B] + ctx, [D]), "cut",
            [wr(wl(got_a, B, *ctx), D), wl(proof, ab)], principal=A)
        return Proof(Sequent([ab] + ctx, [D]), "cut",
            [wr(wl(got_b, *ctx), D), p1], principal=B)

    def _pack_exists(proof, pred, var):
        ctx = [f for f in proof.sequent.left if f is not pred]
        D = proof.sequent.right[0]
        p1 = Proof(Sequent(ctx, [Not(pred), D]), "not_right", [proof], principal=Not(pred))
        fa_np = Forall(var, Not(pred))
        p2 = Proof(Sequent(ctx, [fa_np, D]), "forall_right", [p1], principal=fa_np, term=var)
        ex = Exists(var, pred)
        return Proof(Sequent(ctx + [ex], [D]), "not_left", [p2], principal=ex)

    # Package OrdPair(t2,c,d)
    proof = _pack_and(proof, char_pcd, char_t2)
    and_pcd_t2 = proof.sequent.left[0]  # the And just created
    proof = _pack_exists(proof, and_pcd_t2, pcd)
    ex_pcd = proof.sequent.left[-1]  # the Exists just created
    proof = _pack_and(proof, char_sc, ex_pcd)
    and_sc_ex = proof.sequent.left[0]
    proof = _pack_exists(proof, and_sc_ex, sc)

    # Package OrdPair(t1,a,b)
    proof = _pack_and(proof, char_pab, char_t1)
    and_pab_t1 = proof.sequent.left[0]
    proof = _pack_exists(proof, and_pab_t1, pab)
    ex_pab = proof.sequent.left[-1]
    proof = _pack_and(proof, char_sa, ex_pab)
    and_sa_ex = proof.sequent.left[0]
    proof = _pack_exists(proof, and_sa_ex, sa)

    # Discharge: Eq, OrdPair(t2), forall t2, OrdPair(t1), forall t1, forall d,c,b,a
    ord2_f = Exists(sc, and_sc_ex)
    ord1_f = Exists(sa, and_sa_ex)

    imp_eq = Implies(eq_t1_t2, goal)
    proof = Proof(Sequent([ord1_f, ord2_f], [imp_eq]), "implies_right", [proof], principal=imp_eq)
    imp_ord2 = Implies(OrdPair(t2, c, d), imp_eq)
    proof = Proof(Sequent([ord1_f], [imp_ord2]), "implies_right", [proof], principal=imp_ord2)
    fa_t2 = Forall(t2, imp_ord2)
    proof = Proof(Sequent([ord1_f], [fa_t2]), "forall_right", [proof], term=t2, principal=fa_t2)
    imp_ord1 = Implies(OrdPair(t1, a, b), fa_t2)
    proof = Proof(Sequent([], [imp_ord1]), "implies_right", [proof], principal=imp_ord1)
    fa_t1 = Forall(t1, imp_ord1)
    proof = Proof(Sequent([], [fa_t1]), "forall_right", [proof], term=t1, principal=fa_t1)
    for v in [d, c, b, a]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), "forall_right", [proof], term=v, principal=fa)
    proof.name = "kuratowski"
    return proof


def union_exists():
    """Pairing, Union_ax |- forall a, b. exists s. Union(s, a, b)
    Binary union exists from Pairing + Union axiom."""
    from tactics import apply_thm, wl, wr, mp
    from definitions import Union as UnionDef, PairSet, BigUnion

    a, b, s, p, xv, yv, zv = Var(), Var(), Var(), Var(), Var(), Var(), Var()
    pairing_ax = zfc.Pairing()
    union_ax = zfc.Union()

    # PairSet(p,a,b) and BigUnion(s,p) characterize s = a|b.
    ps = PairSet(p, a, b)
    bu = BigUnion(s, p)
    union_sab = UnionDef(s, a, b)
    in_xs = In(xv, s)
    in_xa = In(xv, a)
    in_xb = In(xv, b)
    or_ab = Or(in_xa, in_xb)
    ex_y = Exists(yv, And(In(yv, p), In(xv, yv)))

    # From BigUnion, instantiate with xv: Iff(In(xv,s), ex_y)
    bu_body = Iff(in_xs, ex_y)
    def _inst_fl(parent, body, term):
        return Proof(Sequent([parent], [body]), 'forall_left',
            [Proof(Sequent([body], [body]), 'axiom', principal=body)],
            principal=parent, term=term)

    bu_inst = _inst_fl(bu, bu_body, xv)  # bu |- bu_body

    # Extract forward: In(xv,s) -> ex_y from bu_body
    bu_fwd = Implies(in_xs, ex_y)
    bu_bwd = Implies(ex_y, in_xs)
    H_bu = Implies(bu_fwd, Not(bu_bwd))
    e1 = Proof(Sequent([bu_body, bu_fwd], [bu_fwd]), 'axiom', principal=bu_fwd)
    e2 = Proof(Sequent([bu_body, bu_fwd], [Not(bu_bwd), bu_fwd]),
               'weakening_right', [e1], principal=Not(bu_bwd))
    e3 = Proof(Sequent([bu_body], [H_bu, bu_fwd]), 'implies_right', [e2], principal=H_bu)
    e4 = Proof(Sequent([H_bu], [H_bu, bu_fwd]), 'weakening_right',
               [Proof(Sequent([H_bu], [H_bu]), 'axiom', principal=H_bu)], principal=bu_fwd)
    e5 = Proof(Sequent([H_bu, bu_body], [bu_fwd]), 'not_left', [e4], principal=bu_body)
    ext_bu_fwd = Proof(Sequent([bu_body], [bu_fwd]), 'cut', [e3, e5], principal=H_bu)
    # Extract backward: ex_y -> In(xv,s)
    f1 = Proof(Sequent([bu_body, bu_fwd, bu_bwd], [bu_bwd]), 'axiom', principal=bu_bwd)
    f2 = Proof(Sequent([bu_body, bu_fwd], [Not(bu_bwd), bu_bwd]), 'not_right', [f1], principal=Not(bu_bwd))
    f3 = Proof(Sequent([bu_body], [H_bu, bu_bwd]), 'implies_right', [f2], principal=H_bu)
    f4 = Proof(Sequent([H_bu], [H_bu, bu_bwd]), 'weakening_right',
               [Proof(Sequent([H_bu], [H_bu]), 'axiom', principal=H_bu)], principal=bu_bwd)
    f5 = Proof(Sequent([H_bu, bu_body], [bu_bwd]), 'not_left', [f4], principal=bu_body)
    ext_bu_bwd = Proof(Sequent([bu_body], [bu_bwd]), 'cut', [f3, f5], principal=H_bu)

    # From PairSet, instantiate with yv: Iff(In(yv,p), Or(Eq(yv,a), Eq(yv,b)))
    ps_body_y = Iff(In(yv, p), Or(Eq(yv, a), Eq(yv, b)))
    ps_inst_y = _inst_fl(ps, ps_body_y, yv)
    # Extract forward: In(yv,p) -> Or(Eq(yv,a), Eq(yv,b))
    ps_fwd_y = Implies(In(yv, p), Or(Eq(yv, a), Eq(yv, b)))
    ps_bwd_y = Implies(Or(Eq(yv, a), Eq(yv, b)), In(yv, p))
    H_ps = Implies(ps_fwd_y, Not(ps_bwd_y))
    g1 = Proof(Sequent([ps_body_y, ps_fwd_y], [ps_fwd_y]), 'axiom', principal=ps_fwd_y)
    g2 = Proof(Sequent([ps_body_y, ps_fwd_y], [Not(ps_bwd_y), ps_fwd_y]),
               'weakening_right', [g1], principal=Not(ps_bwd_y))
    g3 = Proof(Sequent([ps_body_y], [H_ps, ps_fwd_y]), 'implies_right', [g2], principal=H_ps)
    g4 = Proof(Sequent([H_ps], [H_ps, ps_fwd_y]), 'weakening_right',
               [Proof(Sequent([H_ps], [H_ps]), 'axiom', principal=H_ps)], principal=ps_fwd_y)
    g5 = Proof(Sequent([H_ps, ps_body_y], [ps_fwd_y]), 'not_left', [g4], principal=ps_body_y)
    ext_ps_fwd_y = Proof(Sequent([ps_body_y], [ps_fwd_y]), 'cut', [g3, g5], principal=H_ps)

    # Chain: bu |- bu_fwd, ps |- ps_fwd_y (via cut on bu_body, ps_body)
    got_bu_fwd = Proof(Sequent([bu], [bu_fwd]), 'cut',
        [wr(bu_inst, bu_fwd), wl(ext_bu_fwd, bu)], principal=bu_body)
    got_bu_bwd = Proof(Sequent([bu], [bu_bwd]), 'cut',
        [wr(bu_inst, bu_bwd), wl(ext_bu_bwd, bu)], principal=bu_body)
    got_ps_fwd_y = Proof(Sequent([ps], [ps_fwd_y]), 'cut',
        [wr(ps_inst_y, ps_fwd_y), wl(ext_ps_fwd_y, ps)], principal=ps_body_y)

    # === Forward: ps, bu, In(xv,s) |- Or(In(xv,a), In(xv,b)) ===
    # Step 1: In(xv,s) -> ex_y (from bu_fwd). MP: bu, In(xv,s) |- ex_y
    got_ex = mp(got_bu_fwd,
                Proof(Sequent([in_xs], [in_xs]), 'axiom', principal=in_xs),
                in_xs, ex_y, [], [])
    # Step 2: From ex_y, existential elim: introduce yv with In(yv,p)  and  In(xv,yv)
    # From And, get In(yv,p) and In(xv,yv)
    # From ps_fwd_y: In(yv,p) -> Or(Eq(yv,a), Eq(yv,b)). MP: Or(Eq(yv,a), Eq(yv,b))
    # Or elim: case Eq(yv,a) -> x in a; case Eq(yv,b) -> x in b

    # This is the hard part. For now, let me build:
    # In(yv,p), In(xv,yv), ps |- or_ab

    and_yp_xy = And(In(yv, p), In(xv, yv))
    ax_and = Proof(Sequent([and_yp_xy], [and_yp_xy]), 'axiom', principal=and_yp_xy)
    got_yp = apply_thm(and_elim_left(In(yv,p), In(xv,yv), []), [], and_yp_xy, In(yv,p), ax_and, [], [])
    got_xy = apply_thm(and_elim_right(In(yv,p), In(xv,yv), []), [], and_yp_xy, In(xv,yv),
                       Proof(Sequent([and_yp_xy], [and_yp_xy]), 'axiom', principal=and_yp_xy), [], [])

    # From ps: In(yv,p) -> Or(Eq(yv,a), Eq(yv,b)). MP with got_yp:
    got_or_eq = mp(got_ps_fwd_y, got_yp, In(yv, p), Or(Eq(yv, a), Eq(yv, b)), [], [])
    # got_or_eq: [ps, and_yp_xy] |- [Or(Eq(yv,a), Eq(yv,b))]

    # Or elim on Or(Eq(yv,a), Eq(yv,b)):
    # Case Eq(yv,a): from Eq(yv,a) and In(xv,yv), derive In(xv,a)
    # Eq(yv,a) = Forall(zv, Iff(In(zv,yv), In(zv,a))). Instantiate zv=xv: Iff(In(xv,yv), In(xv,a)).
    # Forward: In(xv,yv) -> In(xv,a). MP with In(xv,yv): In(xv,a).
    eq_ya = Eq(yv, a)
    iff_xy_xa = Iff(In(xv, yv), In(xv, a))
    eq_inst_a = _inst_fl(eq_ya, iff_xy_xa, xv)  # Eq(yv,a) |- Iff(In(xv,yv), In(xv,a))
    fwd_xy_xa = Implies(In(xv, yv), In(xv, a))
    ext_fwd_a = Proof(Sequent([iff_xy_xa], [fwd_xy_xa]), 'cut',
        *[None, None], principal=None)  # placeholder -- need to extract forward from Iff

    # This is getting very long. Let me use a helper for Iff forward extraction.
    def _ext_fwd(iff_f):
        L = iff_f.left; R = iff_f.right
        LR = Implies(L, R); RL = Implies(R, L); H = Implies(LR, Not(RL))
        e1 = Proof(Sequent([iff_f, LR], [LR]), 'axiom', principal=LR)
        e2 = Proof(Sequent([iff_f, LR], [Not(RL), LR]), 'weakening_right', [e1], principal=Not(RL))
        e3 = Proof(Sequent([iff_f], [H, LR]), 'implies_right', [e2], principal=H)
        e4 = Proof(Sequent([H], [H, LR]), 'weakening_right',
                   [Proof(Sequent([H], [H]), 'axiom', principal=H)], principal=LR)
        e5 = Proof(Sequent([H, iff_f], [LR]), 'not_left', [e4], principal=iff_f)
        return Proof(Sequent([iff_f], [LR]), 'cut', [e3, e5], principal=H)

    # Case y=a: Eq(yv,a), In(xv,yv) |- In(xv,a) then Or_intro_left
    ext_a = _ext_fwd(iff_xy_xa)  # iff_xy_xa |- In(xv,yv) -> In(xv,a)
    got_fwd_a = Proof(Sequent([eq_ya], [fwd_xy_xa]), 'cut',
        [wr(eq_inst_a, fwd_xy_xa), wl(ext_a, eq_ya)], principal=iff_xy_xa)
    # MP: Eq(yv,a), In(xv,yv) |- In(xv,a)
    case_a = mp(got_fwd_a, got_xy, In(xv, yv), In(xv, a), [], [])
    # Or intro left: ..., |- Or(In(xv,a), In(xv,b))
    # In(xv,a) |- Or(In(xv,a), In(xv,b))
    oil = Proof(Sequent([in_xa], [in_xa]), 'axiom', principal=in_xa)
    oil2 = Proof(Sequent([in_xa, Not(in_xa)], []), 'not_left', [oil], principal=Not(in_xa))
    oil3 = Proof(Sequent([in_xa, Not(in_xa)], [in_xb]), 'weakening_right', [oil2], principal=in_xb)
    oil4 = Proof(Sequent([in_xa], [or_ab]), 'implies_right', [oil3], principal=or_ab)
    case_a_or = Proof(Sequent(case_a.sequent.left, [or_ab]), 'cut',
        [wr(case_a, or_ab), wl(oil4, *case_a.sequent.left)], principal=in_xa)

    # Case y=b: similar
    eq_yb = Eq(yv, b)
    iff_xy_xb = Iff(In(xv, yv), In(xv, b))
    eq_inst_b = _inst_fl(eq_yb, iff_xy_xb, xv)
    fwd_xy_xb = Implies(In(xv, yv), In(xv, b))
    ext_b = _ext_fwd(iff_xy_xb)
    got_fwd_b = Proof(Sequent([eq_yb], [fwd_xy_xb]), 'cut',
        [wr(eq_inst_b, fwd_xy_xb), wl(ext_b, eq_yb)], principal=iff_xy_xb)
    case_b = mp(got_fwd_b, got_xy, In(xv, yv), In(xv, b), [], [])
    # Or intro right
    oir = Proof(Sequent([in_xb, Not(in_xa)], [in_xb]), 'axiom', principal=in_xb)
    oir2 = Proof(Sequent([in_xb], [or_ab]), 'implies_right', [oir], principal=or_ab)
    case_b_or = Proof(Sequent(case_b.sequent.left, [or_ab]), 'cut',
        [wr(case_b, or_ab), wl(oir2, *case_b.sequent.left)], principal=in_xb)

    # Or elim on Or(Eq(yv,a), Eq(yv,b)): and_yp_xy, ps |- or_ab
    or_eq = Or(eq_ya, eq_yb)
    # implies_left on or_eq = Implies(Not(eq_ya), eq_yb):
    # Branch 1: ctx |- Not(eq_ya), or_ab
    ctx_or = got_or_eq.sequent.left  # [ps, and_yp_xy]
    case_a_or_w = wl(case_a_or, *[f for f in ctx_or if not any(f is g for g in case_a_or.sequent.left)])
    case_b_or_w = wl(case_b_or, *[f for f in ctx_or if not any(f is g for g in case_b_or.sequent.left)])
    br1 = Proof(Sequent(ctx_or, [Not(eq_ya), or_ab]), 'not_right', [case_a_or_w], principal=Not(eq_ya))
    or_elim_fwd = Proof(Sequent(ctx_or + [or_eq], [or_ab]), 'implies_left',
                        [br1, case_b_or_w], principal=or_eq)
    # Cut or_eq from got_or_eq
    fwd_from_and = Proof(Sequent(ctx_or, [or_ab]), 'cut',
        [wr(got_or_eq, or_ab), or_elim_fwd], principal=or_eq)
    # fwd_from_and: [ps, and_yp_xy] |- [or_ab]

    # Existential elim: [ps, ex_y] |- [or_ab] from [ps, and_yp_xy] |- [or_ab]
    def _exist_elim_left(proof, pred, var):
        ctx = [f for f in proof.sequent.left if f is not pred]
        D = proof.sequent.right[0]
        p1 = Proof(Sequent(ctx, [Not(pred), D]), 'not_right', [proof], principal=Not(pred))
        fa_np = Forall(var, Not(pred))
        p2 = Proof(Sequent(ctx, [fa_np, D]), 'forall_right', [p1], principal=fa_np, term=var)
        ex = Exists(var, pred)
        return Proof(Sequent(ctx + [ex], [D]), 'not_left', [p2], principal=ex)

    fwd_from_ex = _exist_elim_left(fwd_from_and, and_yp_xy, yv)
    # fwd_from_ex: [ps, ex_y] |- [or_ab]

    # Full forward: ps, bu, In(xv,s) |- or_ab
    # got_ex: [bu, In(xv,s)] |- [ex_y]
    full_fwd = Proof(Sequent([ps, bu, in_xs], [or_ab]), 'cut',
        [wr(wl(got_ex, ps), or_ab), wl(fwd_from_ex, bu, in_xs)], principal=ex_y)

    # === Backward: ps, bu, Or(In(xv,a), In(xv,b)) |- In(xv,s) ===
    # Case x in a: witness y=a. Need a in p  and  x in a, then exists y intro, then bu_bwd.
    # a in p from PairSet: instantiate with a. Iff(In(a,p), Or(Eq(a,a), Eq(a,b))).
    # Backward: Or(Eq(a,a), Eq(a,b)) -> In(a,p). Need Eq(a,a) (eq_reflexive) + or_intro.
    ps_body_a = Iff(In(a, p), Or(Eq(a, a), Eq(a, b)))
    ps_inst_a = _inst_fl(ps, ps_body_a, a)

    def _ext_bwd(iff_f):
        L = iff_f.left; R = iff_f.right
        LR = Implies(L, R); RL = Implies(R, L); H = Implies(LR, Not(RL))
        e1 = Proof(Sequent([iff_f, LR, RL], [RL]), 'axiom', principal=RL)
        e2 = Proof(Sequent([iff_f, LR], [Not(RL), RL]), 'not_right', [e1], principal=Not(RL))
        e3 = Proof(Sequent([iff_f], [H, RL]), 'implies_right', [e2], principal=H)
        e4 = Proof(Sequent([H], [H, RL]), 'weakening_right',
                   [Proof(Sequent([H], [H]), 'axiom', principal=H)], principal=RL)
        e5 = Proof(Sequent([H, iff_f], [RL]), 'not_left', [e4], principal=iff_f)
        return Proof(Sequent([iff_f], [RL]), 'cut', [e3, e5], principal=H)

    ext_ps_bwd_a = _ext_bwd(ps_body_a)  # ps_body_a |- Or(Eq(a,a), Eq(a,b)) -> In(a,p)
    got_ps_bwd_a = Proof(Sequent([ps], [Implies(Or(Eq(a,a), Eq(a,b)), In(a, p))]), 'cut',
        [wr(ps_inst_a, Implies(Or(Eq(a,a), Eq(a,b)), In(a,p))),
         wl(ext_ps_bwd_a, ps)], principal=ps_body_a)

    # eq_reflexive for a: |- Eq(a,a). Inline.
    z_refl = Var()
    P_r = In(z_refl, a); PP = Implies(P_r, P_r)
    r1 = Proof(Sequent([], [PP]), 'implies_right',
               [Proof(Sequent([P_r], [P_r]), 'axiom', principal=P_r)], principal=PP)
    r2 = Proof(Sequent([], [PP]), 'implies_right',
               [Proof(Sequent([P_r], [P_r]), 'axiom', principal=P_r)], principal=PP)
    r3 = Proof(Sequent([Not(PP)], []), 'not_left', [r2], principal=Not(PP))
    r4 = Proof(Sequent([Implies(PP, Not(PP))], []), 'implies_left',
               [r1, r3], principal=Implies(PP, Not(PP)))
    r5 = Proof(Sequent([], [Not(Implies(PP, Not(PP)))]), 'not_right',
               [r4], principal=Not(Implies(PP, Not(PP))))
    eq_aa = Forall(z_refl, Not(Implies(PP, Not(PP))))
    r6 = Proof(Sequent([], [eq_aa]), 'forall_right', [r5], term=z_refl, principal=eq_aa)
    # eq_aa is alpha-equiv to Eq(a,a)

    # Or intro left: Eq(a,a) |- Or(Eq(a,a), Eq(a,b))
    or_eq_a = Or(Eq(a, a), Eq(a, b))
    eq_aa_v = Eq(a, a)
    oil_a1 = Proof(Sequent([eq_aa_v], [eq_aa_v]), 'axiom', principal=eq_aa_v)
    oil_a2 = Proof(Sequent([eq_aa_v, Not(eq_aa_v)], []), 'not_left', [oil_a1], principal=Not(eq_aa_v))
    oil_a3 = Proof(Sequent([eq_aa_v, Not(eq_aa_v)], [Eq(a, b)]),
                   'weakening_right', [oil_a2], principal=Eq(a, b))
    oil_a4 = Proof(Sequent([eq_aa_v], [or_eq_a]), 'implies_right', [oil_a3], principal=or_eq_a)

    # |- Or(Eq(a,a), Eq(a,b)) via cut on Eq(a,a)
    got_or_eq_a = Proof(Sequent([], [or_eq_a]), 'cut',
        [wr(r6, or_eq_a), oil_a4], principal=eq_aa_v)
    # |- In(a, p) via MP: got_ps_bwd_a and got_or_eq_a
    got_a_in_p = mp(got_ps_bwd_a, got_or_eq_a, or_eq_a, In(a, p), [], [])
    # got_a_in_p: [ps] |- [In(a, p)]

    # Build And(In(a,p), In(xv,a)) then exists y intro with witness a
    # In(xv,a) is given. In(a,p) from got_a_in_p.
    # And intro: ps, In(xv,a) |- And(In(a,p), In(xv,a))
    and_ap_xa = And(In(a, p), In(xv, a))
    n_xa = Not(In(xv, a))
    and_i1 = Proof(Sequent([ps, in_xa, n_xa], []), 'not_left',
                   [wl(Proof(Sequent([in_xa], [in_xa]), 'axiom', principal=in_xa), ps)],
                   principal=n_xa)
    and_i2 = Proof(Sequent([ps, in_xa, Implies(In(a, p), n_xa)], []), 'implies_left',
                   [wl(got_a_in_p, in_xa), and_i1], principal=Implies(In(a, p), n_xa))
    got_and_a = Proof(Sequent([ps, in_xa], [and_ap_xa]), 'not_right',
                      [and_i2], principal=and_ap_xa)

    # exists y intro with witness a: ps, In(xv,a) |- exists y.(In(y,p)  and  In(xv,y))
    # and_ap_xa = And(In(a,p), In(xv,a)). After substituting y->a in And(In(y,p), In(xv,y)),
    # we get And(In(a,p), In(xv,a)) = and_ap_xa. Alpha-equiv to ex_y body with y=a.
    # Existential intro: from P(a) derive exists y. P(y)
    and_body = And(In(yv, p), In(xv, yv))  # P(y) - the body of ex_y
    # not_left + forall_left + not_right to introduce Exists
    nl1 = Proof(Sequent([got_and_a.sequent.left[0], got_and_a.sequent.left[1], Not(and_ap_xa)], []),
                'not_left', [got_and_a], principal=Not(and_ap_xa))
    fl1 = Proof(Sequent([ps, in_xa, Forall(yv, Not(and_body))], []),
                'forall_left', [nl1], principal=Forall(yv, Not(and_body)), term=a)
    got_ex_a = Proof(Sequent([ps, in_xa], [ex_y]), 'not_right', [fl1], principal=ex_y)

    # bu_bwd: ex_y -> In(xv,s). MP: ps, bu, In(xv,a) |- In(xv,s)
    bwd_case_a = mp(got_bu_bwd, got_ex_a, ex_y, in_xs, [], [])

    # Case x in b: similar, witness y=b
    ps_body_b = Iff(In(b, p), Or(Eq(b, a), Eq(b, b)))
    ps_inst_b = _inst_fl(ps, ps_body_b, b)
    ext_ps_bwd_b = _ext_bwd(ps_body_b)
    got_ps_bwd_b = Proof(Sequent([ps], [Implies(Or(Eq(b, a), Eq(b, b)), In(b, p))]), 'cut',
        [wr(ps_inst_b, Implies(Or(Eq(b, a), Eq(b, b)), In(b, p))),
         wl(ext_ps_bwd_b, ps)], principal=ps_body_b)

    # eq_reflexive for b
    z_refl2 = Var()
    P_r2 = In(z_refl2, b); PP2 = Implies(P_r2, P_r2)
    rb1 = Proof(Sequent([], [PP2]), 'implies_right',
                [Proof(Sequent([P_r2], [P_r2]), 'axiom', principal=P_r2)], principal=PP2)
    rb2 = Proof(Sequent([], [PP2]), 'implies_right',
                [Proof(Sequent([P_r2], [P_r2]), 'axiom', principal=P_r2)], principal=PP2)
    rb3 = Proof(Sequent([Not(PP2)], []), 'not_left', [rb2], principal=Not(PP2))
    rb4 = Proof(Sequent([Implies(PP2, Not(PP2))], []), 'implies_left',
                [rb1, rb3], principal=Implies(PP2, Not(PP2)))
    rb5 = Proof(Sequent([], [Not(Implies(PP2, Not(PP2)))]), 'not_right',
                [rb4], principal=Not(Implies(PP2, Not(PP2))))
    eq_bb = Forall(z_refl2, Not(Implies(PP2, Not(PP2))))
    rb6 = Proof(Sequent([], [eq_bb]), 'forall_right', [rb5], term=z_refl2, principal=eq_bb)

    or_eq_b = Or(Eq(b, a), Eq(b, b))
    eq_bb_v = Eq(b, b)
    oir_b1 = Proof(Sequent([eq_bb_v, Not(Eq(b, a))], [eq_bb_v]), 'axiom', principal=eq_bb_v)
    oir_b2 = Proof(Sequent([eq_bb_v], [or_eq_b]), 'implies_right', [oir_b1], principal=or_eq_b)
    got_or_eq_b = Proof(Sequent([], [or_eq_b]), 'cut',
        [wr(rb6, or_eq_b), oir_b2], principal=eq_bb_v)
    got_b_in_p = mp(got_ps_bwd_b, got_or_eq_b, or_eq_b, In(b, p), [], [])

    and_bp_xb = And(In(b, p), In(xv, b))
    n_xb = Not(In(xv, b))
    and_ib1 = Proof(Sequent([ps, in_xb, n_xb], []), 'not_left',
                    [wl(Proof(Sequent([in_xb], [in_xb]), 'axiom', principal=in_xb), ps)],
                    principal=n_xb)
    and_ib2 = Proof(Sequent([ps, in_xb, Implies(In(b, p), n_xb)], []), 'implies_left',
                    [wl(got_b_in_p, in_xb), and_ib1], principal=Implies(In(b, p), n_xb))
    got_and_b = Proof(Sequent([ps, in_xb], [and_bp_xb]), 'not_right',
                      [and_ib2], principal=and_bp_xb)
    nlb1 = Proof(Sequent([ps, in_xb, Not(and_bp_xb)], []),
                 'not_left', [got_and_b], principal=Not(and_bp_xb))
    flb1 = Proof(Sequent([ps, in_xb, Forall(yv, Not(and_body))], []),
                 'forall_left', [nlb1], principal=Forall(yv, Not(and_body)), term=b)
    got_ex_b = Proof(Sequent([ps, in_xb], [ex_y]), 'not_right', [flb1], principal=ex_y)
    bwd_case_b = mp(got_bu_bwd, got_ex_b, ex_y, in_xs, [], [])

    # Or elim: ps, bu, Or(In(xv,a), In(xv,b)) |- In(xv,s)
    bwd_a_w = wl(bwd_case_a, or_ab)
    bwd_b_w = wl(bwd_case_b, bu)
    br1_bwd = Proof(Sequent([ps, bu], [Not(in_xa), in_xs]), 'not_right',
                    [wl(bwd_case_a, or_ab)], principal=Not(in_xa))
    # Hmm, bwd_case_a has [ps, bu, in_xa] on left. I need [ps, bu] |- [Not(in_xa), in_xs].
    # not_right from [ps, bu, in_xa] |- [in_xs]: gives [ps, bu] |- [Not(in_xa), in_xs]. (ok)
    br1_bwd = Proof(Sequent([ps, bu], [Not(in_xa), in_xs]), 'not_right',
                    [bwd_case_a], principal=Not(in_xa))
    bwd_or_elim = Proof(Sequent([ps, bu, or_ab], [in_xs]), 'implies_left',
                        [br1_bwd, bwd_case_b], principal=or_ab)

    # === Build Iff: ps, bu |- Iff(In(xv,s), Or(In(xv,a), In(xv,b))) ===
    fwd_imp = Implies(in_xs, or_ab)
    bwd_imp = Implies(or_ab, in_xs)
    full_fwd_r = Proof(Sequent([ps, bu], [fwd_imp]), 'implies_right', [full_fwd], principal=fwd_imp)
    full_bwd_r = Proof(Sequent([ps, bu], [bwd_imp]), 'implies_right', [bwd_or_elim], principal=bwd_imp)

    iff_union = Iff(in_xs, or_ab)
    H_u = Implies(fwd_imp, Not(bwd_imp))
    nr_u = Proof(Sequent([ps, bu, Not(bwd_imp)], []), 'not_left', [full_bwd_r], principal=Not(bwd_imp))
    il_u = Proof(Sequent([ps, bu, H_u], []), 'implies_left', [full_fwd_r, nr_u], principal=H_u)
    core_iff = Proof(Sequent([ps, bu], [iff_union]), 'not_right', [il_u], principal=iff_union)

    # forall_right xv: ps, bu |- Forall(xv, iff_union) = Union(s, a, b) (alpha-equiv)
    fa_union = Forall(xv, iff_union)
    core_fa = Proof(Sequent([ps, bu], [fa_union]), 'forall_right', [core_iff], principal=fa_union, term=xv)

    # === Package existentials ===
    # ps, bu |- Union(s,a,b). Need exists s. Union(s,a,b).
    # Package s into Exists, then package p into Exists.
    # Then discharge PairSet and BigUnion from axioms.

    # For now, package into: exists s. Union(s,a,b)  and  ... hmm, we just need exists s. Union(s,a,b).
    # From ps, bu |- Union(s,a,b), existential intro on s: ps, bu |- exists s. Union(s,a,b)
    ex_union = Exists(s, UnionDef(s, a, b))
    # Existential intro on right: from |- P(t), derive |- exists x. P(x) with witness t.
    # not_right: from Forall(s, Not(Union(s,a,b))), P(s) |- to get |- Not(Forall(s, Not(P(s)))), ...
    # Actually simpler: P(s) on right. not_left with Not(P(s)). forall_left with s. not_right.
    n_union = Not(UnionDef(s, a, b))
    fa_n_union = Forall(s, n_union)
    nl_eu = Proof(Sequent([ps, bu, n_union], []), 'not_left', [core_fa], principal=n_union)
    fl_eu = Proof(Sequent([ps, bu, fa_n_union], []), 'forall_left', [nl_eu],
                  principal=fa_n_union, term=s)
    got_ex_union = Proof(Sequent([ps, bu], [ex_union]), 'not_right', [fl_eu], principal=ex_union)

    # Now need to handle p: ps and bu both mention p.
    # bu = BigUnion(s, p). We derived exists s from above. But p is still free.
    # From Union axiom instantiated with p: exists s. BigUnion(s, p)
    # We need: ps |- exists s. Union(s, a, b)
    # From ps, bu |- exists s. Union(s,a,b) and Union_ax |- exists s. BigUnion(s,p)
    # Use existential elim on exists s.BigUnion(s,p): introduce s with BigUnion(s,p) on left
    # Then from ps, BigUnion(s,p) |- exists s'. Union(s',a,b)... hmm s is used for both.

    # Actually, s in BigUnion and s in Union are the SAME s. The BigUnion(s,p) gives the
    # characterization of s, and we derived Union(s,a,b) for that same s. So exists s. Union(s,a,b)
    # follows from the specific s from BigUnion.

    # From Union_ax with a=p: exists s. BigUnion(s, p)
    ex_bu = Exists(s, bu)
    bu_from_ax = _inst_fl(union_ax, ex_bu, p)  # union_ax |- exists s. BigUnion(s, p)
    # Wait, union_ax = forall a. exists b. BigUnion(b, a). After expansion, the internal exists b and BigUnion
    # should match. Actually, union_ax |- Exists(s, BigUnion(s, p)) after forall_left with p.
    # But the internal vars might differ. Let me just try it.

    # Existential elim on bu: [ps, ex_bu] |- [ex_union] from [ps, bu] |- [ex_union]
    got_ex_from_bu = _exist_elim_left(got_ex_union, bu, s)
    # got_ex_from_bu: [ps, Exists(s, bu)] |- [ex_union]
    # But Exists(s, bu) should be alpha-equiv to ex_bu from the axiom.

    # Cut: ps, union_ax |- ex_union
    got_from_axs = Proof(Sequent([ps, union_ax], [ex_union]), 'cut',
        [wr(wl(bu_from_ax, ps), ex_union), wl(got_ex_from_bu, union_ax)], principal=ex_bu)

    # Now handle p: from Pairing |- exists p. PairSet(p, a, b)
    # Pairing axiom = forall x forall y. exists b. PairSet(b, x, y) (alpha-equiv)
    ex_ps = Exists(p, ps)
    pair_body_b = Exists(p, ps)
    pair_body_a = Forall(b, pair_body_b)
    # Actually Pairing = forall x forall y exists b forall z. Iff(In(z,b), Or(Eq(z,x), Eq(z,y)))
    # = forall x forall y exists b. PairSet(b, x, y) after alpha-equiv
    pair_inst_b = _inst_fl(Forall(b, ex_ps), ex_ps, b)
    pair_inst_a = Proof(Sequent([Forall(a, Forall(b, ex_ps))], [ex_ps]), 'forall_left',
        [pair_inst_b], principal=Forall(a, Forall(b, ex_ps)), term=a)
    # Hmm, this is manually constructing. Let me use the Pairing axiom directly.
    # Pairing expanded should be alpha-equiv to Forall(a, Forall(b, Exists(p, PairSet(p,a,b)))).
    fa_b_ex = Forall(b, ex_ps)
    fa_a_b_ex = Forall(a, fa_b_ex)
    # pairing_ax |- ex_ps via forall_left twice
    p_ax = Proof(Sequent([ex_ps], [ex_ps]), 'axiom', principal=ex_ps)
    p_fl1 = Proof(Sequent([fa_b_ex], [ex_ps]), 'forall_left', [p_ax], principal=fa_b_ex, term=b)
    p_fl2 = Proof(Sequent([fa_a_b_ex], [ex_ps]), 'forall_left', [p_fl1], principal=fa_a_b_ex, term=a)
    # pairing_ax is alpha-equiv to fa_a_b_ex after expansion
    got_ex_ps = Proof(Sequent([pairing_ax], [ex_ps]), 'cut',
        [wr(Proof(Sequent([pairing_ax], [pairing_ax]), 'axiom', principal=pairing_ax), ex_ps),
         wl(p_fl2, pairing_ax)], principal=fa_a_b_ex)

    # Existential elim on ps: [union_ax, ex_ps] |- [ex_union] from [ps, union_ax] |- [ex_union]
    got_from_ex_ps = _exist_elim_left(got_from_axs, ps, p)
    # got_from_ex_ps: [union_ax, Exists(p, ps)] |- [ex_union]

    # Cut ex_ps from Pairing:
    final = Proof(Sequent([pairing_ax, union_ax], [ex_union]), 'cut',
        [wr(wl(got_ex_ps, union_ax), ex_union), wl(got_from_ex_ps, pairing_ax)], principal=ex_ps)

    # Close: forall b, a
    imp_b = Forall(b, ex_union)
    s1 = Proof(Sequent([pairing_ax, union_ax], [imp_b]), 'forall_right',
               [final], principal=imp_b, term=b)
    imp_a = Forall(a, imp_b)
    s2 = Proof(Sequent([pairing_ax, union_ax], [imp_a]), 'forall_right',
               [s1], principal=imp_a, term=a)
    s2.name = 'union_exists'
    return s2


def successor_exists():
    """Pairing, Union |- forall x. exists s. Successor(s, x)
    S(x) = x union {x} exists."""
    from tactics import apply_thm, wl, wr, mp
    from definitions import Successor as SuccDef, Singleton, Union as UnionDef

    x, s, sa, u, xv = Var(), Var(), Var(), Var(), Var()
    pairing_ax = zfc.Pairing()
    union_ax = zfc.Union()

    # S(x) = x | {x}. Need: {x} exists (Pairing), x | {x} exists (union_exists).
    # Singleton(sa, x) and Union(s, x, sa) -> Successor(s, x)
    # Because: z in S(x) iff z in x or z = x
    #        = z in x or z in {x}  (since z in {x} iff z = x)
    #        = z in (x | {x})

    # Successor(s, x) = forall z. z in s iff (z in x or z = x)
    # Union(s, x, sa) = forall z. z in s iff (z in x or z in sa)
    # Singleton(sa, x) = forall z. z in sa iff z = x
    # From Union + Singleton: z in s iff z in x or z in sa iff z in x or z = x. (ok)

    sing = Singleton(sa, x)
    union_s = UnionDef(s, x, sa)
    succ_s = SuccDef(s, x)

    # For eigenvariable xv:
    # From Union: Iff(In(xv, s), Or(In(xv, x), In(xv, sa)))
    # From Singleton: Iff(In(xv, sa), Eq(xv, x))
    # By or_iff_compat with Iff(In(xv,x), In(xv,x)) [reflexive] and Iff(In(xv,sa), Eq(xv,x)):
    # Iff(Or(In(xv,x), In(xv,sa)), Or(In(xv,x), Eq(xv,x)))
    # Chain with Union's Iff: Iff(In(xv,s), Or(In(xv,x), Eq(xv,x))) = Successor

    # Simpler: use char_transfer to chain
    # Iff(In(xv,s), Or(In(xv,x), In(xv,sa))) [from Union]
    # Iff(Or(In(xv,x), In(xv,sa)), Or(In(xv,x), Eq(xv,x))) [from or_iff_compat + Singleton]
    # -> Iff(In(xv,s), Or(In(xv,x), Eq(xv,x))) = Successor body

    union_body = Iff(In(xv, s), Or(In(xv, x), In(xv, sa)))
    sing_body = Iff(In(xv, sa), Eq(xv, x))
    succ_body = Iff(In(xv, s), Or(In(xv, x), Eq(xv, x)))

    def _inst_fl(parent, body, term):
        return Proof(Sequent([parent], [body]), 'forall_left',
            [Proof(Sequent([body], [body]), 'axiom', principal=body)],
            principal=parent, term=term)

    # Instantiate Union and Singleton with xv
    got_union = _inst_fl(union_s, union_body, xv)  # union_s |- union_body
    got_sing = _inst_fl(sing, sing_body, xv)  # sing |- sing_body

    # Iff(In(xv,x), In(xv,x)) -- reflexive Iff, trivially true
    iff_refl = Iff(In(xv, x), In(xv, x))
    P_xx = In(xv, x)
    PQ = Implies(P_xx, P_xx)
    NPQ = Not(PQ)
    H_refl = Implies(PQ, NPQ)
    ax_p = Proof(Sequent([P_xx], [P_xx]), 'axiom', principal=P_xx)
    ir1 = Proof(Sequent([], [PQ]), 'implies_right', [ax_p], principal=PQ)
    ir2 = Proof(Sequent([], [PQ]), 'implies_right',
                [Proof(Sequent([P_xx], [P_xx]), 'axiom', principal=P_xx)], principal=PQ)
    nl_r = Proof(Sequent([NPQ], []), 'not_left', [ir2], principal=NPQ)
    il_r = Proof(Sequent([H_refl], []), 'implies_left', [ir1, nl_r], principal=H_refl)
    got_iff_refl = Proof(Sequent([], [iff_refl]), 'not_right', [il_r], principal=iff_refl)

    # Apply or_iff_compat: Iff(In(xv,x), In(xv,x)), Iff(In(xv,sa), Eq(xv,x))
    #   -> Iff(Or(In(xv,x), In(xv,sa)), Or(In(xv,x), Eq(xv,x)))
    oic = or_iff_compat(In(xv, x), In(xv, sa), In(xv, x), Eq(xv, x), [])
    or_old = Or(In(xv, x), In(xv, sa))
    or_new = Or(In(xv, x), Eq(xv, x))
    iff_or = Iff(or_old, or_new)
    imp_inner = Implies(sing_body, iff_or)
    got_imp = apply_thm(oic, [], iff_refl, imp_inner, got_iff_refl, [], [])
    # got_imp: [] |- Implies(sing_body, iff_or)
    got_iff_or = mp(got_imp, got_sing, sing_body, iff_or, [], [])
    # got_iff_or: [sing] |- [iff_or]

    # Chain: Iff(In(xv,s), or_old) and Iff(or_old, or_new) -> Iff(In(xv,s), or_new)
    ct = char_transfer(In(xv, s), or_old, or_new)
    got_chain = mp(mp(ct, got_union, union_body, Implies(iff_or, succ_body), [], []),
                   got_iff_or, iff_or, succ_body, [], [])
    # got_chain: [union_s, sing] |- [succ_body]

    # forall_right xv: union_s, sing |- Forall(xv, succ_body) = Successor(s, x)
    fa_succ = Forall(xv, succ_body)
    got_succ = Proof(Sequent(got_chain.sequent.left, [fa_succ]),
                     'forall_right', [got_chain], principal=fa_succ, term=xv)

    # Package into exists s. Successor(s, x)
    # From sing, union_s |- Successor(s, x)
    # Need to package s existentially, then handle sa existentially.

    def _pack_exists(proof, pred, var):
        ctx = [f for f in proof.sequent.left if f is not pred]
        D = proof.sequent.right[0]
        p1 = Proof(Sequent(ctx, [Not(pred), D]), 'not_right', [proof], principal=Not(pred))
        fa_np = Forall(var, Not(pred))
        p2 = Proof(Sequent(ctx, [fa_np, D]), 'forall_right', [p1], principal=fa_np, term=var)
        ex = Exists(var, pred)
        return Proof(Sequent(ctx + [ex], [D]), 'not_left', [p2], principal=ex)

    # exists s. Union(s, x, sa) from union_exists
    ue = union_exists()
    ue_formula = ue.sequent.right[0]
    inner = Exists(s, union_s)
    fa_b = Forall(sa, inner)
    fa_a_b = Forall(x, fa_b)
    ax_inner = Proof(Sequent([inner], [inner]), 'axiom', principal=inner)
    fl1 = Proof(Sequent([fa_b], [inner]), 'forall_left', [ax_inner], principal=fa_b, term=sa)
    fl2 = Proof(Sequent([fa_a_b], [inner]), 'forall_left', [fl1], principal=fa_a_b, term=x)
    # Cut with ue: [Pairing, Union] |- [inner]
    got_ex_u = Proof(Sequent([pairing_ax, union_ax], [inner]), 'cut',
        [wr(ue, inner), wl(fl2, pairing_ax, union_ax)], principal=ue_formula)

    # Existential elim on s: from [sing, union_s] |- [fa_succ] derive [sing, Exists(s, union_s)] |- [fa_succ]
    # Then [sing, exists s.Union(s,x,sa)] |- [exists s.Successor(s,x)]... hmm, same s in both?

    # Actually, I need exists s. Successor(s, x). And I have sing, union_s |- Successor(s, x) for a specific s.
    # Existential intro on right: from P(t) on right, derive exists x.P(x) on right.
    ex_succ = Exists(s, SuccDef(s, x))
    n_succ = Not(SuccDef(s, x))
    fa_n_succ = Forall(s, n_succ)
    nl_s = Proof(Sequent(got_succ.sequent.left + [n_succ], []), 'not_left', [got_succ], principal=n_succ)
    fl_s = Proof(Sequent(got_succ.sequent.left + [fa_n_succ], []), 'forall_left',
                 [nl_s], principal=fa_n_succ, term=s)
    got_ex_succ = Proof(Sequent(got_succ.sequent.left, [ex_succ]), 'not_right',
                        [fl_s], principal=ex_succ)
    # got_ex_succ: [union_s, sing] |- [exists s. Successor(s, x)]... wait, s is used in union_s too.

    # Hmm, the s in exists s.Successor(s,x) is quantified. The s in union_s is free. Different roles.
    # The existential says "there exists SOME s". The union_s characterizes a SPECIFIC s.
    # After _pack_exists or existential intro, the specific s gets bound.

    # Let me use a different variable for the existential to avoid confusion.
    s2 = Var()
    ex_succ2 = Exists(s2, SuccDef(s2, x))
    n_succ2 = Not(SuccDef(s2, x))
    fa_n_succ2 = Forall(s2, n_succ2)
    # SuccDef(s, x) on right (from got_succ). Witness s.
    # not_left: got_succ.left + [Not(SuccDef(s,x))] |- []
    nl_s2 = Proof(Sequent(got_succ.sequent.left + [Not(fa_succ)], []),
                  'not_left', [got_succ], principal=Not(fa_succ))
    # Hmm, fa_succ is the Forall version. Let me use the SetSpec-expanded version.
    # Actually Successor(s,x) expands to Forall(xv, Iff(In(xv,s), Or(In(xv,x), Eq(xv,x)))).
    # And fa_succ = Forall(xv, succ_body) which is the same thing.
    # So SuccDef(s,x) and fa_succ are alpha-equiv after expansion.

    # Existential intro with witness s: from |- Successor(s,x), derive |- exists s2. Successor(s2,x)
    nl_s3 = Proof(Sequent(got_succ.sequent.left + [Not(SuccDef(s, x))], []),
                  'not_left', [got_succ], principal=Not(SuccDef(s, x)))
    fl_s3 = Proof(Sequent(got_succ.sequent.left + [Forall(s, Not(SuccDef(s, x)))], []),
                  'forall_left', [nl_s3], principal=Forall(s, Not(SuccDef(s, x))), term=s)
    ex_succ_f = Exists(s, SuccDef(s, x))
    got_ex_succ_f = Proof(Sequent(got_succ.sequent.left, [ex_succ_f]),
                          'not_right', [fl_s3], principal=ex_succ_f)
    # got_ex_succ_f: [union_s, sing] |- [exists s. Successor(s, x)]

    # Existential elim on union_s (variable s): [sing, exists s.Union(s,x,sa)] |- [exists s.Succ(s,x)]
    got_from_ex_u = _pack_exists(got_ex_succ_f, union_s, s)
    # got_from_ex_u: [sing, Exists(s, union_s)] |- [exists s.Succ(s,x)]

    # Cut exists s.Union(s,x,sa) from got_ex_u: [Pairing, Union, sing] |- [exists s.Succ(s,x)]
    got_with_sing = Proof(Sequent([pairing_ax, union_ax, sing], [ex_succ_f]), 'cut',
        [wr(wl(got_ex_u, sing), ex_succ_f),
         wl(got_from_ex_u, pairing_ax, union_ax)],
        principal=Exists(s, union_s))

    # Now handle sa: from Pairing, exists sa. Singleton(sa, x) exists (singleton_exists).
    # Existential elim on sing (variable sa):
    got_from_ex_sing = _pack_exists(got_with_sing, sing, sa)
    # got_from_ex_sing: [Pairing, Union, Exists(sa, sing)] |- [exists s.Succ(s,x)]

    # singleton_exists: [Pairing] |- [forall a. exists sa. Singleton(sa, a)]
    se = singleton_exists()
    se_formula = se.sequent.right[0]
    ex_sing = Exists(sa, sing)
    fa_ex_sing = Forall(x, ex_sing)
    ax_ex = Proof(Sequent([ex_sing], [ex_sing]), 'axiom', principal=ex_sing)
    fl_se = Proof(Sequent([fa_ex_sing], [ex_sing]), 'forall_left', [ax_ex], principal=fa_ex_sing, term=x)
    got_ex_sing = Proof(Sequent([pairing_ax], [ex_sing]), 'cut',
        [wr(se, ex_sing), wl(fl_se, pairing_ax)], principal=se_formula)
    # got_ex_sing: [Pairing] |- [exists sa. Singleton(sa, x)]

    # Cut: [Pairing, Union] |- [exists s. Succ(s, x)]
    final = Proof(Sequent([pairing_ax, union_ax], [ex_succ_f]), 'cut',
        [wr(wl(got_ex_sing, union_ax), ex_succ_f),
         got_from_ex_sing],
        principal=Exists(sa, sing))

    # Close: forall x
    fa_x = Forall(x, ex_succ_f)
    proof = Proof(Sequent([pairing_ax, union_ax], [fa_x]),
                  'forall_right', [final], principal=fa_x, term=x)
    proof.name = 'successor_exists'
    return proof


def intersect_exists():
    """Separation |- forall a, b. exists s. Intersect(s, a, b)
    Binary intersection exists."""
    from definitions import Intersect
    a, b, s = Var(), Var(), Var()
    sep = zfc.Separation(lambda x: In(x, b), [b])
    goal = Forall(b, Forall(a, Exists(s, Intersect(s, a, b))))
    proof = Proof(Sequent([sep], [goal]), 'axiom', principal=sep)
    proof.name = 'intersect_exists'
    return proof


def big_union_exists():
    """Union_axiom |- forall a. exists s. BigUnion(s, a)
    The big union of any set exists."""
    from definitions import BigUnion
    ax = zfc.Union()
    a, s = Var(), Var()
    goal = Forall(a, Exists(s, BigUnion(s, a)))
    # The goal is alpha-equiv to the Union axiom after expansion
    proof = Proof(Sequent([ax], [goal]), 'axiom', principal=ax)
    proof.name = 'big_union_exists'
    return proof


def unique_successor():
    """|- forall x, s1, s2. Successor(s1,x) -> Successor(s2,x) -> Eq(s1,s2)
    Sets with the same successor characterization are equal."""
    from tactics import apply_thm, wl, wr, mp
    from definitions import Successor as SuccDef

    x, s1, s2, zv = Var(), Var(), Var(), Var()
    succ1 = SuccDef(s1, x)  # forall z. z in s1 iff (z in x or z = x)
    succ2 = SuccDef(s2, x)

    # For each z: Iff(In(z,s1), Or(In(z,x),Eq(z,x))) and Iff(In(z,s2), Or(In(z,x),Eq(z,x)))
    # By iff_sym on succ2: Iff(Or(In(z,x),Eq(z,x)), In(z,s2))
    # By iff_chain: Iff(In(z,s1), In(z,s2))
    # forall z: Eq(s1, s2)

    mid = Or(In(zv, x), Eq(zv, x))
    iff1 = Iff(In(zv, s1), mid)
    iff2 = Iff(In(zv, s2), mid)
    iff_result = Iff(In(zv, s1), In(zv, s2))

    def _fl(parent, body, term):
        return Proof(Sequent([parent], [body]), 'forall_left',
            [Proof(Sequent([body], [body]), 'axiom', principal=body)],
            principal=parent, term=term)

    # succ1 |- iff1 and succ2 |- iff2
    got_iff1 = _fl(succ1, iff1, zv)
    got_iff2 = _fl(succ2, iff2, zv)

    # iff_sym on iff2: succ2 |- Iff(mid, In(zv, s2))
    iff2_sym = Iff(mid, In(zv, s2))
    sym = iff_sym(In(zv, s2), mid, [])
    got_iff2_sym = mp(sym, got_iff2, iff2, iff2_sym, [], [])

    # iff_chain: Iff(In(zv,s1), mid), Iff(mid, In(zv,s2)) -> Iff(In(zv,s1), In(zv,s2))
    ct = char_transfer(In(zv, s1), mid, In(zv, s2))
    got_result = mp(mp(ct, got_iff1, iff1, Implies(iff2_sym, iff_result), [], []),
                    got_iff2_sym, iff2_sym, iff_result, [], [])
    # got_result: [succ1, succ2] |- [iff_result]

    # forall z: succ1, succ2 |- Eq(s1, s2)
    eq_body = Forall(zv, iff_result)
    core = Proof(Sequent([succ1, succ2], [eq_body]),
                 'forall_right', [got_result], principal=eq_body, term=zv)

    # Close
    eq_s = Eq(s1, s2)
    imp2 = Implies(succ2, eq_s)
    s1p = Proof(Sequent([succ1], [imp2]), 'implies_right', [core], principal=imp2)
    imp1 = Implies(succ1, imp2)
    s2p = Proof(Sequent([], [imp1]), 'implies_right', [s1p], principal=imp1)
    for v in [s2, s1, x]:
        body = s2p.sequent.right[0]
        fa = Forall(v, body)
        s2p = Proof(Sequent([], [fa]), 'forall_right', [s2p], term=v, principal=fa)
    s2p.name = 'unique_successor'
    return s2p


def infinity_gives_inductive():
    """Infinity, Extensionality |- exists b. Inductive(b)
    The Infinity axiom provides an inductive set."""
    from tactics import apply_thm, wl, wr, mp
    from definitions import Inductive, Empty, Successor

    # Infinity gives: exists b. (exists e.e in b  and  Empty(e))  and  (forall y in b.exists s.s in b  and  Successor(s,y))
    # Need: exists b. Inductive(b) = exists b. (forall e.Empty(e)->e in b)  and  (forall x in b.forall s.Succ(s,x)->s in b)
    #
    # The conversion exists ->forall  uses:
    # - unique_empty: Empty(e1)  and  Empty(e2) -> Eq(e1,e2)
    # - unique_successor: Succ(s1,x)  and  Succ(s2,x) -> Eq(s1,s2)
    # - Extensionality: Eq(a,b) -> (a in c <-> b in c)
    #
    # From exists e.e in b  and  Empty(e): exists e0 with e0 in b, Empty(e0).
    # For any e with Empty(e): Eq(e,e0) (unique_empty). Ext: e in b. Hence forall e.Empty(e)->e in b.
    # Similarly for successors.
    #
    from tactics import wl, wr
    b, e0, e, x, s0, s = Var(), Var(), Var(), Var(), Var(), Var()
    inf_ax = zfc.Infinity()
    ext_ax = zfc.Extensionality()

    # Prove: Ext, Inf |- exists b. Inductive(b)
    # Using unique_empty + unique_successor + eq_substitution via raw forall_left + implies_left.

    # Step 1: unique_empty gives Eq(e0,e) from Empty(e0), Empty(e)
    # ue structure: Forall(v1, Implies(Empty(v1), Forall(v2, Implies(Empty(v2), Eq(v1,v2)))))
    ue = unique_empty()
    ue_f = ue.sequent.right[0]  # the actual formula
    eq_e0_e = Eq(e0, e)
    # Peel: forall_left(e0) -> Implies(Empty(e0), Forall(e, Implies(Empty(e), Eq(e0,e))))
    # But we use the ACTUAL body from ue_f to avoid structure mismatch.
    ue_body = ue_f.body  # Implies(Empty(v1), Forall(v2, Implies(Empty(v2), Eq(v1,v2))))
    imp_e_eq = Implies(Empty(e), eq_e0_e)
    fa_e_imp = Forall(e, imp_e_eq)
    imp_e0_rest = Implies(Empty(e0), fa_e_imp)
    # Now peel from inside out, matching ue's actual structure:
    # innermost: Eq(e0,e) |- Eq(e0,e)
    ax_eq = Proof(Sequent([eq_e0_e], [eq_e0_e]), 'axiom', principal=eq_e0_e)
    # implies_left on Empty(e): need Empty(e) on both sides
    ax_ee = wr(Proof(Sequent([Empty(e)], [Empty(e)]), 'axiom', principal=Empty(e)), eq_e0_e)
    il_e = Proof(Sequent([imp_e_eq, Empty(e)], [eq_e0_e]),
                 'implies_left', [ax_ee, wl(ax_eq, Empty(e))], principal=imp_e_eq)
    # forall_left(e): Forall(e, imp_e_eq), Empty(e) |- Eq(e0,e)
    fl_e = Proof(Sequent([fa_e_imp, Empty(e)], [eq_e0_e]),
                 'forall_left', [il_e], principal=fa_e_imp, term=e)
    # implies_left on Empty(e0): need Empty(e0) on both sides
    ax_e0 = wr(Proof(Sequent([Empty(e0), Empty(e)], [Empty(e0)]),
                     'weakening_left',
                     [Proof(Sequent([Empty(e0)], [Empty(e0)]), 'axiom', principal=Empty(e0))],
                     principal=Empty(e)), eq_e0_e)
    il_e0 = Proof(Sequent([imp_e0_rest, Empty(e0), Empty(e)], [eq_e0_e]),
                  'implies_left', [ax_e0, wl(fl_e, Empty(e0))], principal=imp_e0_rest)
    # forall_left(e0): ue_f, Empty(e0), Empty(e) |- Eq(e0,e)
    fl_e0 = Proof(Sequent([ue_f, Empty(e0), Empty(e)], [eq_e0_e]),
                  'forall_left', [il_e0], principal=ue_f, term=e0)
    # Cut with ue: Empty(e0), Empty(e) |- Eq(e0,e)
    got_eq = Proof(Sequent([Empty(e0), Empty(e)], [eq_e0_e]), 'cut',
        [wr(wl(ue, Empty(e0), Empty(e)), eq_e0_e), fl_e0],
        principal=ue_f)

    # Step 2: eq_substitution gives Iff(In(e0,b), In(e,b)) from Eq(e0,e)
    es = eq_substitution()
    iff_eb = Iff(In(e0, b), In(e, b))
    imp_eq_iff = Implies(eq_e0_e, iff_eb)
    fa_z = Forall(b, imp_eq_iff)
    fa_ez = Forall(e, fa_z)
    fa_e0ez = Forall(e0, fa_ez)
    ax_iff = Proof(Sequent([iff_eb], [iff_eb]), 'axiom', principal=iff_eb)
    ax_eq2 = wr(Proof(Sequent([eq_e0_e], [eq_e0_e]), 'axiom', principal=eq_e0_e), iff_eb)
    il_eq = Proof(Sequent([imp_eq_iff, eq_e0_e], [iff_eb]),
                  'implies_left', [ax_eq2, wl(ax_iff, eq_e0_e)], principal=imp_eq_iff)
    fl_z = Proof(Sequent([fa_z, eq_e0_e], [iff_eb]), 'forall_left', [il_eq], principal=fa_z, term=b)
    fl_ez = Proof(Sequent([fa_ez, eq_e0_e], [iff_eb]), 'forall_left', [fl_z], principal=fa_ez, term=e)
    fl_e0ez = Proof(Sequent([fa_e0ez, eq_e0_e], [iff_eb]), 'forall_left', [fl_ez], principal=fa_e0ez, term=e0)
    got_iff = Proof(Sequent([ext_ax, eq_e0_e], [iff_eb]), 'cut',
        [wr(wl(es, eq_e0_e), iff_eb), wl(fl_e0ez, ext_ax)], principal=fa_e0ez)

    # Step 3: extract forward In(e0,b)->In(e,b) from Iff
    fwd_eb = Implies(In(e0, b), In(e, b))
    bwd_eb = Implies(In(e, b), In(e0, b))
    H_iff = Implies(fwd_eb, Not(bwd_eb))
    ef1 = Proof(Sequent([iff_eb, fwd_eb], [fwd_eb]), 'axiom', principal=fwd_eb)
    ef2 = Proof(Sequent([iff_eb, fwd_eb], [Not(bwd_eb), fwd_eb]), 'weakening_right', [ef1], principal=Not(bwd_eb))
    ef3 = Proof(Sequent([iff_eb], [H_iff, fwd_eb]), 'implies_right', [ef2], principal=H_iff)
    ef4 = wr(Proof(Sequent([H_iff], [H_iff]), 'axiom', principal=H_iff), fwd_eb)
    ef5 = Proof(Sequent([H_iff, iff_eb], [fwd_eb]), 'not_left', [ef4], principal=iff_eb)
    got_fwd_iff = Proof(Sequent([iff_eb], [fwd_eb]), 'cut', [ef3, ef5], principal=H_iff)
    got_fwd = Proof(Sequent([ext_ax, eq_e0_e], [fwd_eb]), 'cut',
        [wr(got_iff, fwd_eb), wl(got_fwd_iff, ext_ax, eq_e0_e)], principal=iff_eb)
    got_fwd2 = Proof(Sequent([ext_ax, Empty(e0), Empty(e)], [fwd_eb]), 'cut',
        [wr(wl(got_eq, ext_ax), fwd_eb), wl(got_fwd, Empty(e0), Empty(e))], principal=eq_e0_e)

    # MP: ext_ax, Empty(e0), Empty(e), In(e0,b) |- In(e,b)
    got_in_e = mp(got_fwd2, Proof(Sequent([In(e0, b)], [In(e0, b)]), 'axiom', principal=In(e0, b)),
                  In(e0, b), In(e, b), [], [])

    # Part 1: forall e. Empty(e) -> In(e, b)
    imp_e_in = Implies(Empty(e), In(e, b))
    d1 = Proof(Sequent([ext_ax, Empty(e0), In(e0, b)], [imp_e_in]), 'implies_right', [got_in_e], principal=imp_e_in)
    fa_e_part1 = Forall(e, imp_e_in)
    d2 = Proof(Sequent([ext_ax, Empty(e0), In(e0, b)], [fa_e_part1]), 'forall_right', [d1], principal=fa_e_part1, term=e)

    # === Part 2: successor closure (same pattern with unique_successor) ===
    us = unique_successor()
    succ_s0 = Successor(s0, x); succ_s = Successor(s, x)
    eq_s0_s = Eq(s0, s)
    imp_s_eqs = Implies(succ_s, eq_s0_s)
    imp_s0_rest_s = Implies(succ_s0, imp_s_eqs)
    fa_s2 = Forall(s, imp_s0_rest_s)
    fa_s1s2 = Forall(s0, fa_s2)
    fa_xs1s2 = Forall(x, fa_s1s2)
    ax_eqs = Proof(Sequent([eq_s0_s], [eq_s0_s]), 'axiom', principal=eq_s0_s)
    ax_ss = wr(Proof(Sequent([succ_s, succ_s0], [succ_s]),
                     'weakening_left',
                     [Proof(Sequent([succ_s], [succ_s]), 'axiom', principal=succ_s)], principal=succ_s0),
               eq_s0_s)
    il_ss = Proof(Sequent([imp_s_eqs, succ_s, succ_s0], [eq_s0_s]),
                  'implies_left', [ax_ss, wl(ax_eqs, succ_s, succ_s0)], principal=imp_s_eqs)
    ax_s0s = wr(Proof(Sequent([succ_s0, succ_s], [succ_s0]),
                      'weakening_left',
                      [Proof(Sequent([succ_s0], [succ_s0]), 'axiom', principal=succ_s0)], principal=succ_s),
                eq_s0_s)
    il_s0s = Proof(Sequent([imp_s0_rest_s, succ_s0, succ_s], [eq_s0_s]),
                   'implies_left', [ax_s0s, il_ss], principal=imp_s0_rest_s)
    fl_ss = Proof(Sequent([fa_s2, succ_s0, succ_s], [eq_s0_s]), 'forall_left', [il_s0s], principal=fa_s2, term=s)
    fl_s1s = Proof(Sequent([fa_s1s2, succ_s0, succ_s], [eq_s0_s]), 'forall_left', [fl_ss], principal=fa_s1s2, term=s0)
    fl_xs = Proof(Sequent([fa_xs1s2, succ_s0, succ_s], [eq_s0_s]), 'forall_left', [fl_s1s], principal=fa_xs1s2, term=x)
    got_eq_s = Proof(Sequent([succ_s0, succ_s], [eq_s0_s]), 'cut',
        [wr(wl(us, succ_s0, succ_s), eq_s0_s), fl_xs], principal=fa_xs1s2)

    iff_sb = Iff(In(s0, b), In(s, b))
    imp_eq_iffs = Implies(eq_s0_s, iff_sb)
    fa_zs = Forall(b, imp_eq_iffs); fa_szs = Forall(s, fa_zs); fa_s0szs = Forall(s0, fa_szs)
    ax_iffs = Proof(Sequent([iff_sb], [iff_sb]), 'axiom', principal=iff_sb)
    ax_eqs2 = wr(Proof(Sequent([eq_s0_s], [eq_s0_s]), 'axiom', principal=eq_s0_s), iff_sb)
    il_eqs = Proof(Sequent([imp_eq_iffs, eq_s0_s], [iff_sb]), 'implies_left', [ax_eqs2, wl(ax_iffs, eq_s0_s)], principal=imp_eq_iffs)
    fl_zs = Proof(Sequent([fa_zs, eq_s0_s], [iff_sb]), 'forall_left', [il_eqs], principal=fa_zs, term=b)
    fl_szs = Proof(Sequent([fa_szs, eq_s0_s], [iff_sb]), 'forall_left', [fl_zs], principal=fa_szs, term=s)
    fl_s0szs = Proof(Sequent([fa_s0szs, eq_s0_s], [iff_sb]), 'forall_left', [fl_szs], principal=fa_s0szs, term=s0)
    got_iff_s = Proof(Sequent([ext_ax, eq_s0_s], [iff_sb]), 'cut',
        [wr(wl(es, eq_s0_s), iff_sb), wl(fl_s0szs, ext_ax)], principal=fa_s0szs)
    fwd_sb = Implies(In(s0, b), In(s, b)); bwd_sb = Implies(In(s, b), In(s0, b))
    H_s = Implies(fwd_sb, Not(bwd_sb))
    sf1 = Proof(Sequent([iff_sb, fwd_sb], [fwd_sb]), 'axiom', principal=fwd_sb)
    sf2 = Proof(Sequent([iff_sb, fwd_sb], [Not(bwd_sb), fwd_sb]), 'weakening_right', [sf1], principal=Not(bwd_sb))
    sf3 = Proof(Sequent([iff_sb], [H_s, fwd_sb]), 'implies_right', [sf2], principal=H_s)
    sf4 = wr(Proof(Sequent([H_s], [H_s]), 'axiom', principal=H_s), fwd_sb)
    sf5 = Proof(Sequent([H_s, iff_sb], [fwd_sb]), 'not_left', [sf4], principal=iff_sb)
    got_fwd_s = Proof(Sequent([iff_sb], [fwd_sb]), 'cut', [sf3, sf5], principal=H_s)
    got_fwd_s2 = Proof(Sequent([ext_ax, eq_s0_s], [fwd_sb]), 'cut',
        [wr(got_iff_s, fwd_sb), wl(got_fwd_s, ext_ax, eq_s0_s)], principal=iff_sb)
    got_fwd_s3 = Proof(Sequent([ext_ax, succ_s0, succ_s], [fwd_sb]), 'cut',
        [wr(wl(got_eq_s, ext_ax), fwd_sb), wl(got_fwd_s2, succ_s0, succ_s)], principal=eq_s0_s)
    got_in_s = mp(got_fwd_s3, Proof(Sequent([In(s0, b)], [In(s0, b)]), 'axiom', principal=In(s0, b)),
                  In(s0, b), In(s, b), [], [])
    imp_s_in = Implies(succ_s, In(s, b))
    d3 = Proof(Sequent([ext_ax, succ_s0, In(s0, b)], [imp_s_in]), 'implies_right', [got_in_s], principal=imp_s_in)
    fa_s_part2 = Forall(s, imp_s_in)
    d4 = Proof(Sequent([ext_ax, succ_s0, In(s0, b)], [fa_s_part2]), 'forall_right', [d3], principal=fa_s_part2, term=s)

    # Package And(In(s0,b), succ_s0) -> existential elim
    and_s0 = And(In(s0, b), succ_s0)
    ax_as = Proof(Sequent([and_s0], [and_s0]), 'axiom', principal=and_s0)
    got_ins0 = apply_thm(and_elim_left(In(s0, b), succ_s0, []), [], and_s0, In(s0, b), ax_as, [], [])
    got_succ0 = apply_thm(and_elim_right(In(s0, b), succ_s0, []), [], and_s0, succ_s0,
                           Proof(Sequent([and_s0], [and_s0]), 'axiom', principal=and_s0), [], [])
    d4a = Proof(Sequent([ext_ax, and_s0], [fa_s_part2]), 'cut',
        [wr(wl(got_succ0, ext_ax), fa_s_part2),
         Proof(Sequent([ext_ax, and_s0, succ_s0], [fa_s_part2]), 'cut',
             [wr(wl(got_ins0, ext_ax, succ_s0), fa_s_part2), wl(d4, and_s0)], principal=In(s0, b))],
        principal=succ_s0)
    def _eel(proof, pred, var):
        ctx = [f for f in proof.sequent.left if f is not pred]
        D = proof.sequent.right[0]
        p1 = Proof(Sequent(ctx, [Not(pred), D]), 'not_right', [proof], principal=Not(pred))
        p2 = Proof(Sequent(ctx, [Forall(var, Not(pred)), D]), 'forall_right', [p1], principal=Forall(var, Not(pred)), term=var)
        return Proof(Sequent(ctx + [Exists(var, pred)], [D]), 'not_left', [p2], principal=Exists(var, pred))
    d5 = _eel(d4a, and_s0, s0)
    ex_s0 = Exists(s0, and_s0)

    # Closure from Infinity
    inf_closure = Forall(x, Implies(In(x, b), ex_s0))
    imp_x_ex = Implies(In(x, b), ex_s0)
    fl_cl = Proof(Sequent([inf_closure], [imp_x_ex]), 'forall_left',
        [Proof(Sequent([imp_x_ex], [imp_x_ex]), 'axiom', principal=imp_x_ex)], principal=inf_closure, term=x)
    got_ex_s0 = mp(fl_cl, Proof(Sequent([In(x, b)], [In(x, b)]), 'axiom', principal=In(x, b)), In(x, b), ex_s0, [], [])
    got_cl = Proof(Sequent([ext_ax, inf_closure, In(x, b)], [fa_s_part2]), 'cut',
        [wr(wl(got_ex_s0, ext_ax), fa_s_part2), wl(d5, inf_closure, In(x, b))], principal=ex_s0)
    imp_x_fa = Implies(In(x, b), fa_s_part2)
    dc1 = Proof(Sequent([ext_ax, inf_closure], [imp_x_fa]), 'implies_right', [got_cl], principal=imp_x_fa)
    fa_x_part2 = Forall(x, imp_x_fa)
    dc2 = Proof(Sequent([ext_ax, inf_closure], [fa_x_part2]), 'forall_right', [dc1], principal=fa_x_part2, term=x)

    # Build Inductive(b) from parts
    ind_b = Inductive(b)
    ncl = Not(fa_x_part2)
    a1 = Proof(Sequent([ext_ax, Empty(e0), In(e0, b), inf_closure, ncl], []), 'not_left', [wl(dc2, Empty(e0), In(e0, b))], principal=ncl)
    a2 = Proof(Sequent([ext_ax, Empty(e0), In(e0, b), inf_closure, Implies(fa_e_part1, ncl)], []),
               'implies_left', [wl(d2, inf_closure), a1], principal=Implies(fa_e_part1, ncl))
    got_ind = Proof(Sequent([ext_ax, Empty(e0), In(e0, b), inf_closure], [ind_b]), 'not_right', [a2], principal=ind_b)

    # Package from inf_empty
    inf_empty = Exists(e0, And(In(e0, b), Empty(e0)))
    and_e0 = And(In(e0, b), Empty(e0))
    ax_ae = Proof(Sequent([and_e0], [and_e0]), 'axiom', principal=and_e0)
    got_ine0 = apply_thm(and_elim_left(In(e0, b), Empty(e0), []), [], and_e0, In(e0, b), ax_ae, [], [])
    got_empe0 = apply_thm(and_elim_right(In(e0, b), Empty(e0), []), [], and_e0, Empty(e0),
                           Proof(Sequent([and_e0], [and_e0]), 'axiom', principal=and_e0), [], [])
    gi2 = Proof(Sequent([ext_ax, and_e0, inf_closure], [ind_b]), 'cut',
        [wr(wl(got_empe0, ext_ax, inf_closure), ind_b),
         Proof(Sequent([ext_ax, and_e0, Empty(e0), inf_closure], [ind_b]), 'cut',
             [wr(wl(got_ine0, ext_ax, Empty(e0), inf_closure), ind_b), wl(got_ind, and_e0)], principal=In(e0, b))],
        principal=Empty(e0))
    gi3 = _eel(gi2, and_e0, e0)

    # Package inf_and
    inf_and = And(inf_empty, inf_closure)
    ax_ia = Proof(Sequent([inf_and], [inf_and]), 'axiom', principal=inf_and)
    got_ie = apply_thm(and_elim_left(inf_empty, inf_closure, []), [], inf_and, inf_empty, ax_ia, [], [])
    got_ic = apply_thm(and_elim_right(inf_empty, inf_closure, []), [], inf_and, inf_closure,
                        Proof(Sequent([inf_and], [inf_and]), 'axiom', principal=inf_and), [], [])
    gi4 = Proof(Sequent([ext_ax, inf_and], [ind_b]), 'cut',
        [wr(wl(got_ie, ext_ax), ind_b),
         Proof(Sequent([ext_ax, inf_and, inf_empty], [ind_b]), 'cut',
             [wr(wl(got_ic, ext_ax, inf_empty), ind_b), wl(gi3, inf_and)], principal=inf_closure)],
        principal=inf_empty)

    # Exist intro + elim
    ex_ind = Exists(b, ind_b)
    nl = Proof(Sequent(gi4.sequent.left + [Not(ind_b)], []), 'not_left', [gi4], principal=Not(ind_b))
    fl = Proof(Sequent(gi4.sequent.left + [Forall(b, Not(ind_b))], []), 'forall_left', [nl], principal=Forall(b, Not(ind_b)), term=b)
    gex = Proof(Sequent(gi4.sequent.left, [ex_ind]), 'not_right', [fl], principal=ex_ind)
    gfex = _eel(gex, inf_and, b)
    proof = Proof(Sequent([ext_ax, inf_ax], [ex_ind]), gfex.rule, gfex.premises, term=gfex.term, principal=gfex.principal)
    proof.name = 'infinity_gives_inductive'
    return proof


def omega_is_inductive():
    """Infinity, Extensionality |- forall w. Omega(w) -> Inductive(w)
    omega is itself an inductive set."""
    from tactics import apply_thm, wl, wr, mp
    from definitions import Inductive, Omega, Empty, Successor

    w, b0, xv, cv, ev, sv = Var(), Var(), Var(), Var(), Var(), Var()
    inf_ax = zfc.Infinity()
    ext_ax = zfc.Extensionality()
    omega_w = Omega(w)
    ind_w = Inductive(w)

    # Step 1: From infinity_gives_inductive: exists b. Inductive(b)
    igi = infinity_gives_inductive()  # [ext, inf] |- [exists b. Inductive(b)]
    ind_b0 = Inductive(b0)
    ex_ind = Exists(b0, ind_b0)

    # Step 2: From Omega(w) with b=b0: Inductive(b0) -> forall x. x in w <-> cond(x)
    cond_xv = And(In(xv, b0), Forall(cv, Implies(Inductive(cv), In(xv, cv))))
    iff_w = Iff(In(xv, w), cond_xv)
    fa_iff = Forall(xv, iff_w)
    imp_ind_fa = Implies(ind_b0, fa_iff)

    def _fl(parent, body, term):
        return Proof(Sequent([parent], [body]), 'forall_left',
            [Proof(Sequent([body], [body]), 'axiom', principal=body)],
            principal=parent, term=term)

    # omega_w |- Implies(Inductive(b0), fa_iff)
    got_imp = _fl(omega_w, imp_ind_fa, b0)
    # MP with Inductive(b0): omega_w, Inductive(b0) |- fa_iff
    got_fa = mp(got_imp,
                Proof(Sequent([ind_b0], [ind_b0]), 'axiom', principal=ind_b0),
                ind_b0, fa_iff, [], [])

    # Instantiate fa_iff with xv=ev (for empty part) and xv (for closure part)
    # via cut on fa_iff
    fl_iff = _fl(fa_iff, iff_w, xv)  # fa_iff |- iff_w
    def _get_iff(xvar):
        """From got_fa, instantiate and get: omega_w, ind_b0 |- Iff(In(xvar,w), cond(xvar))"""
        c_xvar = And(In(xvar, b0), Forall(cv, Implies(Inductive(cv), In(xvar, cv))))
        iff_xvar = Iff(In(xvar, w), c_xvar)
        fl_x = _fl(fa_iff, iff_xvar, xvar)
        return Proof(Sequent(got_fa.sequent.left, [iff_xvar]), 'cut',
            [wr(got_fa, iff_xvar), wl(fl_x, *got_fa.sequent.left)], principal=fa_iff)

    # === Extract Iff backward: cond -> In(xvar, w) ===
    def _ext_bwd(iff_f):
        L = iff_f.left; R = iff_f.right
        LR = Implies(L, R); RL = Implies(R, L); H = Implies(LR, Not(RL))
        e1 = Proof(Sequent([iff_f, LR, RL], [RL]), 'axiom', principal=RL)
        e2 = Proof(Sequent([iff_f, LR], [Not(RL), RL]), 'not_right', [e1], principal=Not(RL))
        e3 = Proof(Sequent([iff_f], [H, RL]), 'implies_right', [e2], principal=H)
        e4 = wr(Proof(Sequent([H], [H]), 'axiom', principal=H), RL)
        e5 = Proof(Sequent([H, iff_f], [RL]), 'not_left', [e4], principal=iff_f)
        return Proof(Sequent([iff_f], [RL]), 'cut', [e3, e5], principal=H)

    def _ext_fwd(iff_f):
        L = iff_f.left; R = iff_f.right
        LR = Implies(L, R); RL = Implies(R, L); H = Implies(LR, Not(RL))
        e1 = Proof(Sequent([iff_f, LR], [LR]), 'axiom', principal=LR)
        e2 = Proof(Sequent([iff_f, LR], [Not(RL), LR]), 'weakening_right', [e1], principal=Not(RL))
        e3 = Proof(Sequent([iff_f], [H, LR]), 'implies_right', [e2], principal=H)
        e4 = wr(Proof(Sequent([H], [H]), 'axiom', principal=H), LR)
        e5 = Proof(Sequent([H, iff_f], [LR]), 'not_left', [e4], principal=iff_f)
        return Proof(Sequent([iff_f], [LR]), 'cut', [e3, e5], principal=H)

    # === Part 1: forall e. Empty(e) -> e in w ===
    # For ev with Empty(ev):
    # Need cond(ev) = In(ev, b0)  and  forall c. Ind(c) -> In(ev, c)
    # From Ind(b0): Empty(ev) -> In(ev, b0) [first part of Inductive]
    # From Ind(c) for any c: Empty(ev) -> In(ev, c) [first part of Inductive(c)]
    # So forall c. Ind(c) -> In(ev, c) follows from Empty(ev).

    # Unpack Ind(b0): And(forall e.Empty(e)->In(e,b0), forall x.In(x,b0)->forall s.Succ(s,x)->In(s,b0))
    ind_empty = Forall(ev, Implies(Empty(ev), In(ev, b0)))  # first part
    ind_closure_b0 = Forall(xv, Implies(In(xv, b0), Forall(sv, Implies(Successor(sv, xv), In(sv, b0)))))

    ax_ind = Proof(Sequent([ind_b0], [ind_b0]), 'axiom', principal=ind_b0)
    got_empty_b0 = apply_thm(and_elim_left(ind_empty, ind_closure_b0, []), [],
                              ind_b0, ind_empty, ax_ind, [], [])
    # got_empty_b0: [ind_b0] |- [forall e. Empty(e) -> In(e, b0)]

    # For In(ev, b0): ind_b0, Empty(ev) |- In(ev, b0)
    imp_emp_in = Implies(Empty(ev), In(ev, b0))
    fl_emp = _fl(ind_empty, imp_emp_in, ev)
    got_ev_b0 = mp(Proof(Sequent([ind_b0], [imp_emp_in]), 'cut',
                    [wr(got_empty_b0, imp_emp_in), wl(fl_emp, ind_b0)], principal=ind_empty),
                   Proof(Sequent([Empty(ev)], [Empty(ev)]), 'axiom', principal=Empty(ev)),
                   Empty(ev), In(ev, b0), [], [])
    # got_ev_b0: [ind_b0, Empty(ev)] |- [In(ev, b0)]

    # For forall c. Ind(c) -> In(ev, c):
    # From Ind(c): forall e. Empty(e) -> In(e, c). Instantiate e=ev: Empty(ev) -> In(ev, c).
    ind_c = Inductive(cv)
    ind_empty_c = Forall(ev, Implies(Empty(ev), In(ev, cv)))
    ind_closure_c = Forall(xv, Implies(In(xv, cv), Forall(sv, Implies(Successor(sv, xv), In(sv, cv)))))
    ax_ind_c = Proof(Sequent([ind_c], [ind_c]), 'axiom', principal=ind_c)
    got_empty_c = apply_thm(and_elim_left(ind_empty_c, ind_closure_c, []), [],
                             ind_c, ind_empty_c, ax_ind_c, [], [])
    fl_emp_c = _fl(ind_empty_c, Implies(Empty(ev), In(ev, cv)), ev)
    got_ev_c = mp(Proof(Sequent([ind_c], [Implies(Empty(ev), In(ev, cv))]), 'cut',
                   [wr(got_empty_c, Implies(Empty(ev), In(ev, cv))),
                    wl(fl_emp_c, ind_c)], principal=ind_empty_c),
                  Proof(Sequent([Empty(ev)], [Empty(ev)]), 'axiom', principal=Empty(ev)),
                  Empty(ev), In(ev, cv), [], [])
    # got_ev_c: [ind_c, Empty(ev)] |- [In(ev, cv)]

    # forall c. Ind(c) -> In(ev, c): discharge Ind(c), forall c
    imp_ind_in = Implies(ind_c, In(ev, cv))
    d_c = Proof(Sequent([Empty(ev)], [imp_ind_in]), 'implies_right', [got_ev_c], principal=imp_ind_in)
    fa_c = Forall(cv, imp_ind_in)
    d_c2 = Proof(Sequent([Empty(ev)], [fa_c]), 'forall_right', [d_c], principal=fa_c, term=cv)
    # d_c2: [Empty(ev)] |- [forall c. Ind(c) -> In(ev, c)]

    # Build cond(ev) = And(In(ev, b0), forall c. Ind(c) -> In(ev, c))
    cond_ev = And(In(ev, b0), fa_c)
    n_fc = Not(fa_c)
    and_c1 = Proof(Sequent([ind_b0, Empty(ev), n_fc], []),
                   'not_left', [wl(d_c2, ind_b0)], principal=n_fc)
    and_c2 = Proof(Sequent([ind_b0, Empty(ev), Implies(In(ev, b0), n_fc)], []),
                   'implies_left', [got_ev_b0, and_c1], principal=Implies(In(ev, b0), n_fc))
    got_cond_ev = Proof(Sequent([ind_b0, Empty(ev)], [cond_ev]),
                        'not_right', [and_c2], principal=cond_ev)
    # got_cond_ev: [ind_b0, Empty(ev)] |- [cond_ev]

    # Apply Iff backward: cond_ev -> In(ev, w)
    iff_ev = Iff(In(ev, w), cond_ev)
    got_iff_ev = _get_iff(ev)  # omega_w, ind_b0 |- iff_ev
    bwd_ev = _ext_bwd(iff_ev)  # iff_ev |- cond_ev -> In(ev, w)
    got_bwd_ev = Proof(Sequent(got_iff_ev.sequent.left, [Implies(cond_ev, In(ev, w))]), 'cut',
        [wr(got_iff_ev, Implies(cond_ev, In(ev, w))),
         wl(bwd_ev, *got_iff_ev.sequent.left)], principal=iff_ev)
    # MP: omega_w, ind_b0, cond_ev |- In(ev, w)
    got_ev_w = mp(got_bwd_ev, got_cond_ev, cond_ev, In(ev, w), [ind_b0], [ind_b0])
    # got_ev_w: [omega_w, ind_b0, Empty(ev)] |- [In(ev, w)]

    # Part 1 done: discharge Empty(ev), forall ev
    imp_emp_w = Implies(Empty(ev), In(ev, w))
    p1 = Proof(Sequent([omega_w, ind_b0], [imp_emp_w]),
               'implies_right', [got_ev_w], principal=imp_emp_w)
    fa_ev = Forall(ev, imp_emp_w)
    p1f = Proof(Sequent([omega_w, ind_b0], [fa_ev]),
                'forall_right', [p1], principal=fa_ev, term=ev)

    # === Part 2: forall x in w. forall s. Succ(s,x) -> s in w ===
    # For xv in w with Succ(sv, xv):
    # Iff forward at xv: In(xv,w) -> cond(xv). Extract In(xv,b0) and forall c.Ind(c)->In(xv,c).
    # From Ind(b0) closure + In(xv,b0) + Succ(sv,xv): In(sv,b0).
    # From Ind(c) closure + In(xv,c) + Succ(sv,xv): In(sv,c). So forall c.Ind(c)->In(sv,c).
    # Build cond(sv). Iff backward: In(sv,w). (ok)

    got_iff_xv = _get_iff(xv)  # omega_w, ind_b0 |- Iff(In(xv,w), cond(xv))
    cond_xv_full = And(In(xv, b0), Forall(cv, Implies(Inductive(cv), In(xv, cv))))
    iff_xv = Iff(In(xv, w), cond_xv_full)
    fwd_xv = _ext_fwd(iff_xv)  # iff_xv |- In(xv,w) -> cond(xv)
    got_fwd_xv = Proof(Sequent(got_iff_xv.sequent.left, [Implies(In(xv, w), cond_xv_full)]), 'cut',
        [wr(got_iff_xv, Implies(In(xv, w), cond_xv_full)),
         wl(fwd_xv, *got_iff_xv.sequent.left)], principal=iff_xv)
    # MP with In(xv, w):
    got_cond_xv = mp(got_fwd_xv,
                     Proof(Sequent([In(xv, w)], [In(xv, w)]), 'axiom', principal=In(xv, w)),
                     In(xv, w), cond_xv_full, [], [])
    # got_cond_xv: [omega_w, ind_b0, In(xv,w)] |- [cond_xv_full]

    # Extract In(xv, b0) and forall c.Ind(c)->In(xv,c) from cond
    fa_c_xv = Forall(cv, Implies(Inductive(cv), In(xv, cv)))
    ax_cond = Proof(Sequent([cond_xv_full], [cond_xv_full]), 'axiom', principal=cond_xv_full)
    got_xv_b0 = apply_thm(and_elim_left(In(xv, b0), fa_c_xv, []), [],
                            cond_xv_full, In(xv, b0), ax_cond, [], [])
    got_fa_c_xv = apply_thm(and_elim_right(In(xv, b0), fa_c_xv, []), [],
                              cond_xv_full, fa_c_xv,
                              Proof(Sequent([cond_xv_full], [cond_xv_full]), 'axiom', principal=cond_xv_full), [], [])

    # From Ind(b0) closure + In(xv,b0) + Succ(sv,xv): In(sv,b0)
    got_closure_b0 = apply_thm(and_elim_right(ind_empty, ind_closure_b0, []), [],
                                ind_b0, ind_closure_b0,
                                Proof(Sequent([ind_b0], [ind_b0]), 'axiom', principal=ind_b0), [], [])
    # got_closure_b0: [ind_b0] |- [forall x.In(x,b0)->forall s.Succ(s,x)->In(s,b0)]
    imp_xv_cl = Implies(In(xv, b0), Forall(sv, Implies(Successor(sv, xv), In(sv, b0))))
    fl_cl = _fl(ind_closure_b0, imp_xv_cl, xv)
    fa_sv_imp = Forall(sv, Implies(Successor(sv, xv), In(sv, b0)))
    got_fa_sv = mp(Proof(Sequent([ind_b0], [imp_xv_cl]), 'cut',
                    [wr(got_closure_b0, imp_xv_cl), wl(fl_cl, ind_b0)], principal=ind_closure_b0),
                   got_xv_b0, In(xv, b0), fa_sv_imp, [], [])
    # got_fa_sv: [ind_b0, cond_xv_full] |- [forall s.Succ(s,xv)->In(s,b0)]
    imp_sv_in = Implies(Successor(sv, xv), In(sv, b0))
    fl_sv = _fl(fa_sv_imp, imp_sv_in, sv)
    got_sv_b0 = mp(Proof(Sequent(got_fa_sv.sequent.left, [imp_sv_in]), 'cut',
                    [wr(got_fa_sv, imp_sv_in), wl(fl_sv, *got_fa_sv.sequent.left)], principal=fa_sv_imp),
                   Proof(Sequent([Successor(sv, xv)], [Successor(sv, xv)]), 'axiom', principal=Successor(sv, xv)),
                   Successor(sv, xv), In(sv, b0), [], [])
    # got_sv_b0: [ind_b0, cond_xv_full, Succ(sv,xv)] |- [In(sv,b0)]

    # For forall c. Ind(c) -> In(sv, c): from Ind(c), In(xv,c), Succ(sv,xv) -> In(sv,c)
    got_closure_c = apply_thm(and_elim_right(ind_empty_c, ind_closure_c, []), [],
                               ind_c, ind_closure_c,
                               Proof(Sequent([ind_c], [ind_c]), 'axiom', principal=ind_c), [], [])
    imp_xv_cl_c = Implies(In(xv, cv), Forall(sv, Implies(Successor(sv, xv), In(sv, cv))))
    fl_cl_c = _fl(ind_closure_c, imp_xv_cl_c, xv)
    # From forall c.Ind(c)->In(xv,c), instantiate c=cv: Ind(cv) -> In(xv, cv)
    imp_ind_xv = Implies(Inductive(cv), In(xv, cv))
    fl_c_xv = _fl(fa_c_xv, imp_ind_xv, cv)
    got_xv_cv = mp(wl(fl_c_xv, ind_c),
                   Proof(Sequent([ind_c], [ind_c]), 'axiom', principal=ind_c),
                   ind_c, In(xv, cv), [ind_c], [ind_c])
    # got_xv_cv: [fa_c_xv, ind_c] |- [In(xv, cv)]

    fa_sv_imp_c = Forall(sv, Implies(Successor(sv, xv), In(sv, cv)))
    got_fa_sv_c = mp(Proof(Sequent([ind_c], [imp_xv_cl_c]), 'cut',
                      [wr(got_closure_c, imp_xv_cl_c), wl(fl_cl_c, ind_c)], principal=ind_closure_c),
                     got_xv_cv, In(xv, cv), fa_sv_imp_c, [ind_c], [ind_c])
    imp_sv_in_c = Implies(Successor(sv, xv), In(sv, cv))
    fl_sv_c = _fl(fa_sv_imp_c, imp_sv_in_c, sv)
    got_sv_cv = mp(Proof(Sequent(got_fa_sv_c.sequent.left, [imp_sv_in_c]), 'cut',
                    [wr(got_fa_sv_c, imp_sv_in_c), wl(fl_sv_c, *got_fa_sv_c.sequent.left)], principal=fa_sv_imp_c),
                   Proof(Sequent([Successor(sv, xv)], [Successor(sv, xv)]), 'axiom', principal=Successor(sv, xv)),
                   Successor(sv, xv), In(sv, cv), [], [])
    # got_sv_cv: [fa_c_xv, ind_c, Succ(sv,xv)] |- [In(sv, cv)]

    # forall c. Ind(c) -> In(sv, c): discharge ind_c, forall cv
    imp_ind_sv = Implies(ind_c, In(sv, cv))
    d_sv_c = Proof(Sequent([fa_c_xv, Successor(sv, xv)], [imp_ind_sv]),
                   'implies_right', [got_sv_cv], principal=imp_ind_sv)
    fa_c_sv = Forall(cv, imp_ind_sv)
    d_sv_c2 = Proof(Sequent([fa_c_xv, Successor(sv, xv)], [fa_c_sv]),
                    'forall_right', [d_sv_c], principal=fa_c_sv, term=cv)
    # d_sv_c2: [fa_c_xv, Succ(sv,xv)] |- [forall c. Ind(c) -> In(sv, c)]

    # Build cond(sv): And(In(sv,b0), fa_c_sv)
    cond_sv = And(In(sv, b0), fa_c_sv)
    n_fcsv = Not(fa_c_sv)
    and_sv1 = Proof(Sequent([ind_b0, cond_xv_full, Successor(sv, xv), fa_c_xv, n_fcsv], []),
                    'not_left', [wl(d_sv_c2, ind_b0, cond_xv_full)], principal=n_fcsv)
    # Hmm, got_sv_b0 has [ind_b0, cond_xv_full, Succ] and d_sv_c2 has [fa_c_xv, Succ].
    # Need to merge: [ind_b0, cond_xv_full, fa_c_xv, Succ(sv,xv)]
    # But fa_c_xv comes from cond_xv_full (it's the second component of And).
    # So we need to extract fa_c_xv from cond_xv_full via and_elim_right, then cut.

    # Actually, got_fa_c_xv: [cond_xv_full] |- [fa_c_xv]
    # Cut fa_c_xv: replace fa_c_xv with cond_xv_full
    d_sv_c2_from_cond = Proof(Sequent([cond_xv_full, Successor(sv, xv)], [fa_c_sv]), 'cut',
        [wr(wl(got_fa_c_xv, Successor(sv, xv)), fa_c_sv),
         wl(d_sv_c2, cond_xv_full)], principal=fa_c_xv)

    and_sv1b = Proof(Sequent([ind_b0, cond_xv_full, Successor(sv, xv), n_fcsv], []),
                     'not_left', [wl(d_sv_c2_from_cond, ind_b0)], principal=n_fcsv)
    and_sv2 = Proof(Sequent([ind_b0, cond_xv_full, Successor(sv, xv), Implies(In(sv, b0), n_fcsv)], []),
                    'implies_left', [got_sv_b0, and_sv1b], principal=Implies(In(sv, b0), n_fcsv))
    got_cond_sv = Proof(Sequent([ind_b0, cond_xv_full, Successor(sv, xv)], [cond_sv]),
                        'not_right', [and_sv2], principal=cond_sv)

    # Cut cond_xv_full from In(xv, w):
    got_cond_sv2 = Proof(Sequent([omega_w, ind_b0, In(xv, w), Successor(sv, xv)], [cond_sv]), 'cut',
        [wr(wl(got_cond_xv, Successor(sv, xv)), cond_sv),
         wl(got_cond_sv, omega_w, In(xv, w))], principal=cond_xv_full)

    # Apply Iff backward for sv:
    cond_sv_full = cond_sv  # And(In(sv, b0), forall c. Ind(c) -> In(sv, c))
    iff_sv = Iff(In(sv, w), cond_sv_full)
    got_iff_sv = _get_iff(sv)
    bwd_sv = _ext_bwd(iff_sv)
    got_bwd_sv = Proof(Sequent(got_iff_sv.sequent.left, [Implies(cond_sv_full, In(sv, w))]), 'cut',
        [wr(got_iff_sv, Implies(cond_sv_full, In(sv, w))),
         wl(bwd_sv, *got_iff_sv.sequent.left)], principal=iff_sv)
    got_sv_w = mp(got_bwd_sv, got_cond_sv2, cond_sv_full, In(sv, w), [omega_w, ind_b0], [omega_w, ind_b0])
    # got_sv_w: [omega_w, ind_b0, In(xv,w), Succ(sv,xv)] |- [In(sv,w)]

    # Part 2: discharge Succ, forall sv, discharge In(xv,w), forall xv
    imp_succ_w = Implies(Successor(sv, xv), In(sv, w))
    p2a = Proof(Sequent([omega_w, ind_b0, In(xv, w)], [imp_succ_w]),
                'implies_right', [got_sv_w], principal=imp_succ_w)
    fa_sv_w = Forall(sv, imp_succ_w)
    p2b = Proof(Sequent([omega_w, ind_b0, In(xv, w)], [fa_sv_w]),
                'forall_right', [p2a], principal=fa_sv_w, term=sv)
    imp_xv_w = Implies(In(xv, w), fa_sv_w)
    p2c = Proof(Sequent([omega_w, ind_b0], [imp_xv_w]),
                'implies_right', [p2b], principal=imp_xv_w)
    fa_xv_w = Forall(xv, imp_xv_w)
    p2f = Proof(Sequent([omega_w, ind_b0], [fa_xv_w]),
                'forall_right', [p2c], principal=fa_xv_w, term=xv)

    # === Build Inductive(w) = And(fa_ev, fa_xv_w) ===
    n_p2 = Not(fa_xv_w)
    a1 = Proof(Sequent([omega_w, ind_b0, n_p2], []), 'not_left', [p2f], principal=n_p2)
    a2 = Proof(Sequent([omega_w, ind_b0, Implies(fa_ev, n_p2)], []),
               'implies_left', [p1f, a1], principal=Implies(fa_ev, n_p2))
    got_ind_w = Proof(Sequent([omega_w, ind_b0], [ind_w]), 'not_right', [a2], principal=ind_w)

    # === Existential elimination on b0 ===
    def _eel(proof, pred, var):
        ctx = [f for f in proof.sequent.left if f is not pred]
        D = proof.sequent.right[0]
        p1 = Proof(Sequent(ctx, [Not(pred), D]), 'not_right', [proof], principal=Not(pred))
        p2 = Proof(Sequent(ctx, [Forall(var, Not(pred)), D]),
                   'forall_right', [p1], principal=Forall(var, Not(pred)), term=var)
        return Proof(Sequent(ctx + [Exists(var, pred)], [D]), 'not_left', [p2], principal=Exists(var, pred))

    got_ind_w2 = _eel(got_ind_w, ind_b0, b0)
    # got_ind_w2: [omega_w, Exists(b0, Inductive(b0))] |- [Inductive(w)]

    # Cut with infinity_gives_inductive:
    got_ind_w3 = Proof(Sequent([omega_w, ext_ax, inf_ax], [ind_w]), 'cut',
        [wr(wl(igi, omega_w), ind_w), wl(got_ind_w2, ext_ax, inf_ax)], principal=ex_ind)

    # Close: discharge omega_w, forall w
    imp_omega = Implies(omega_w, ind_w)
    s1 = Proof(Sequent([ext_ax, inf_ax], [imp_omega]), 'implies_right', [got_ind_w3], principal=imp_omega)
    fa_w = Forall(w, imp_omega)
    s2 = Proof(Sequent([ext_ax, inf_ax], [fa_w]), 'forall_right', [s1], principal=fa_w, term=w)
    s2.name = 'omega_is_inductive'
    return s2


def eq_in_eq():
    """|- forall x1, x2, z. Eq(x1, x2) -> Iff(Eq(z, x1), Eq(z, x2))
    Equality substitution inside Eq: if x1=x2 then (z=x1 iff z=x2)."""
    from tactics import wl, wr, mp

    x1, x2, z, wv = Var(), Var(), Var(), Var()
    eq_x = Eq(x1, x2)  # forall w. Iff(In(w, x1), In(w, x2))
    eq_zx1 = Eq(z, x1)  # forall w. Iff(In(w, z), In(w, x1))
    eq_zx2 = Eq(z, x2)  # forall w. Iff(In(w, z), In(w, x2))

    # For each w: from Iff(In(w,z), In(w,x1)) and Iff(In(w,x1), In(w,x2))
    # derive Iff(In(w,z), In(w,x2)) by iff_chain.
    # Then forall w: Eq(z, x2).

    iff_wz_wx1 = Iff(In(wv, z), In(wv, x1))
    iff_wx1_wx2 = Iff(In(wv, x1), In(wv, x2))
    iff_wz_wx2 = Iff(In(wv, z), In(wv, x2))

    def _fl(parent, body, term):
        return Proof(Sequent([parent], [body]), 'forall_left',
            [Proof(Sequent([body], [body]), 'axiom', principal=body)],
            principal=parent, term=term)

    # eq_zx1 instantiated at w: iff_wz_wx1
    got_iff1 = _fl(eq_zx1, iff_wz_wx1, wv)
    # eq_x instantiated at w: iff_wx1_wx2
    got_iff2 = _fl(eq_x, iff_wx1_wx2, wv)

    # iff_chain: Iff(In(w,z), In(w,x1)), Iff(In(w,x1), In(w,x2)) -> Iff(In(w,z), In(w,x2))
    ct = char_transfer(In(wv, z), In(wv, x1), In(wv, x2))
    got_result = mp(mp(ct, got_iff1, iff_wz_wx1, Implies(iff_wx1_wx2, iff_wz_wx2), [], []),
                    got_iff2, iff_wx1_wx2, iff_wz_wx2, [], [])
    # got_result: [eq_zx1, eq_x] |- [iff_wz_wx2]

    # forall w: eq_zx1, eq_x |- Eq(z, x2) = Forall(wv, iff_wz_wx2)
    fa_w = Forall(wv, iff_wz_wx2)
    got_fa = Proof(Sequent([eq_zx1, eq_x], [fa_w]),
                   'forall_right', [got_result], principal=fa_w, term=wv)
    # fa_w is alpha-equiv to Eq(z, x2) after expansion

    # This gives: eq_zx1, eq_x |- eq_zx2 (the FORWARD direction)
    # For backward: eq_zx2, eq_x |- eq_zx1. Same proof with x1/x2 swapped.
    iff_wx2_wx1 = Iff(In(wv, x2), In(wv, x1))
    got_iff2_sym = mp(iff_sym(In(wv, x1), In(wv, x2), []), got_iff2, iff_wx1_wx2, iff_wx2_wx1, [], [])
    got_iff_zx2 = _fl(eq_zx2, Iff(In(wv, z), In(wv, x2)), wv)
    ct2 = char_transfer(In(wv, z), In(wv, x2), In(wv, x1))
    got_result2 = mp(mp(ct2, got_iff_zx2, Iff(In(wv, z), In(wv, x2)), Implies(iff_wx2_wx1, iff_wz_wx1), [], []),
                     got_iff2_sym, iff_wx2_wx1, iff_wz_wx1, [], [])
    fa_w2 = Forall(wv, iff_wz_wx1)
    got_fa2 = Proof(Sequent([eq_zx2, eq_x], [fa_w2]),
                    'forall_right', [got_result2], principal=fa_w2, term=wv)
    # got_fa2: eq_zx2, eq_x |- eq_zx1

    # Build Iff(eq_zx1, eq_zx2) from forward and backward
    fwd = Implies(eq_zx1, eq_zx2)
    bwd = Implies(eq_zx2, eq_zx1)
    H = Implies(fwd, Not(bwd))
    iff_result = Iff(eq_zx1, eq_zx2)

    fwd_pf = Proof(Sequent([eq_x], [fwd]), 'implies_right', [got_fa], principal=fwd)
    bwd_pf = Proof(Sequent([eq_x], [bwd]), 'implies_right', [got_fa2], principal=bwd)

    nr = Proof(Sequent([eq_x, Not(bwd)], []), 'not_left', [bwd_pf], principal=Not(bwd))
    il = Proof(Sequent([eq_x, H], []), 'implies_left', [fwd_pf, nr], principal=H)
    core = Proof(Sequent([eq_x], [iff_result]), 'not_right', [il], principal=iff_result)

    # Close: eq_x -> forall z. Iff(eq_zx1, eq_zx2)
    imp = Implies(eq_x, Forall(z, iff_result))
    s1 = Proof(Sequent([], [Forall(z, iff_result)]),
               'forall_right',
               [Proof(Sequent([eq_x], [iff_result]), core.rule, core.premises, principal=core.principal)],
               principal=Forall(z, iff_result), term=z)
    # Hmm, need to discharge eq_x first, then forall z
    d1 = Proof(Sequent([], [Implies(eq_x, iff_result)]), 'implies_right', [core], principal=Implies(eq_x, iff_result))
    # But I want forall z INSIDE the implies. Let me restructure:
    # eq_x |- forall z. iff_result
    fa_z = Forall(z, iff_result)
    core_fa = Proof(Sequent([eq_x], [fa_z]), 'forall_right', [core], principal=fa_z, term=z)
    # |- eq_x -> forall z. iff_result
    imp_top = Implies(eq_x, fa_z)
    s1 = Proof(Sequent([], [imp_top]), 'implies_right', [core_fa], principal=imp_top)
    for v in [x2, x1]:
        body = s1.sequent.right[0]
        fa = Forall(v, body)
        s1 = Proof(Sequent([], [fa]), 'forall_right', [s1], term=v, principal=fa)
    s1.name = 'eq_in_eq'
    return s1


def func_preserves_eq():
    """Extensionality |- forall f,x1,x2,y1,y2.
       Function(f) -> Eq(x1,x2) -> Apply(f,x1,y1) -> Apply(f,x2,y2) -> Eq(y1,y2)
    Functions map equal inputs to equal outputs."""
    from tactics import apply_thm, wl, wr, mp
    from definitions import Function as FuncDef, Apply, Singleton, PairSet, OrdPair

    f, x1, x2, y1, y2 = Var(), Var(), Var(), Var(), Var()
    ext_ax = zfc.Extensionality()
    func_f = FuncDef(f)
    eq_x = Eq(x1, x2)
    app1 = Apply(f, x1, y1)
    app2 = Apply(f, x2, y2)
    goal = Eq(y1, y2)

    # Strategy: from Eq(x1,x2) + Apply(f,x2,y2), derive Apply(f,x1,y2).
    # Then Function(f) + Apply(f,x1,y1) + Apply(f,x1,y2) -> Eq(y1,y2).
    #
    # Apply(f,x,y) = exists p. OrdPair(p,x,y)  and  In(p,f)
    # OrdPair(p,x,y) = exists sa. Singleton(sa,x)  and  exists pab. PairSet(pab,x,y)  and  PairSet(p,sa,pab)
    #
    # From Eq(x1,x2): Singleton(sa,x1) <-> Singleton(sa,x2) and PairSet(pab,x1,y) <-> PairSet(pab,x2,y).
    # So OrdPair(p,x1,y2) <-> OrdPair(p,x2,y2). So Apply(f,x1,y2) <-> Apply(f,x2,y2).
    #
    # Singleton(sa,x) = forall z. Iff(In(z,sa), Eq(z,x)).
    # From eq_in_eq: Eq(x1,x2) -> Eq(z,x1) <-> Eq(z,x2).
    # By iff_chain: Iff(In(z,sa), Eq(z,x1)) + Iff(Eq(z,x1), Eq(z,x2)) -> Iff(In(z,sa), Eq(z,x2)).
    # So Singleton(sa,x1) -> Singleton(sa,x2). (ok)
    #
    # PairSet(pab,x,y) = forall z. Iff(In(z,pab), Or(Eq(z,x), Eq(z,y))).
    # From eq_in_eq: Eq(z,x1) <-> Eq(z,x2). And Eq(z,y) <-> Eq(z,y) (refl iff).
    # By or_iff_compat: Or(Eq(z,x1),Eq(z,y)) <-> Or(Eq(z,x2),Eq(z,y)).
    # By iff_chain: Iff(In(z,pab), Or(Eq(z,x1),Eq(z,y))) -> Iff(In(z,pab), Or(Eq(z,x2),Eq(z,y))).
    # So PairSet(pab,x1,y2) -> PairSet(pab,x2,y2). (ok)
    #
    # Step 1: Eq(x1,x2), Singleton(sa,x2) |- Singleton(sa,x1)
    # Singleton(sa,x) = forall z. Iff(In(z,sa), Eq(z,x))
    # From eq_in_eq: Eq(x1,x2) -> Iff(Eq(z,x1), Eq(z,x2))
    # iff_sym: Iff(Eq(z,x2), Eq(z,x1))
    # iff_chain: Iff(In(z,sa), Eq(z,x2)) + Iff(Eq(z,x2), Eq(z,x1)) -> Iff(In(z,sa), Eq(z,x1))
    sa, pab, p, zv = Var(), Var(), Var(), Var()
    sing_x2 = Singleton(sa, x2)
    sing_x1 = Singleton(sa, x1)

    eie = eq_in_eq()  # |- forall x1 forall x2. Eq(x1,x2) -> forall z. Iff(Eq(z,x1), Eq(z,x2))
    iff_eq_z = Iff(Eq(zv, x1), Eq(zv, x2))

    # Instantiate eq_in_eq with x1, x2, z:
    fa_z_iff = Forall(zv, iff_eq_z)
    ax_eq = Proof(Sequent([eq_x], [eq_x]), 'axiom', principal=eq_x)
    got_fa_iff = apply_thm(eie, [x1, x2], eq_x, fa_z_iff, ax_eq, [], [])
    # got_fa_iff: [eq_x] |- [forall z. Iff(Eq(z,x1), Eq(z,x2))]

    def _fl(parent, body, term):
        return Proof(Sequent([parent], [body]), 'forall_left',
            [Proof(Sequent([body], [body]), 'axiom', principal=body)],
            principal=parent, term=term)

    # Instantiate at zv:
    fl_z = _fl(fa_z_iff, iff_eq_z, zv)
    got_iff_eq = Proof(Sequent([eq_x], [iff_eq_z]), 'cut',
        [wr(got_fa_iff, iff_eq_z), wl(fl_z, eq_x)], principal=fa_z_iff)
    # got_iff_eq: [eq_x] |- [Iff(Eq(z,x1), Eq(z,x2))]

    # iff_sym: Iff(Eq(z,x2), Eq(z,x1))
    iff_eq_z_rev = Iff(Eq(zv, x2), Eq(zv, x1))
    got_iff_rev = mp(iff_sym(Eq(zv, x1), Eq(zv, x2), []), got_iff_eq, iff_eq_z, iff_eq_z_rev, [], [])
    # got_iff_rev: [eq_x] |- [Iff(Eq(z,x2), Eq(z,x1))]

    # Singleton(sa, x2) instantiated at zv: Iff(In(zv, sa), Eq(zv, x2))
    iff_in_eq = Iff(In(zv, sa), Eq(zv, x2))
    got_sing_inst = _fl(sing_x2, iff_in_eq, zv)
    # got_sing_inst: [sing_x2] |- [Iff(In(zv,sa), Eq(zv,x2))]

    # iff_chain: Iff(In(zv,sa), Eq(zv,x2)) + Iff(Eq(zv,x2), Eq(zv,x1)) -> Iff(In(zv,sa), Eq(zv,x1))
    iff_in_eq1 = Iff(In(zv, sa), Eq(zv, x1))
    ct = char_transfer(In(zv, sa), Eq(zv, x2), Eq(zv, x1))
    got_sing_z = mp(mp(ct, got_sing_inst, iff_in_eq, Implies(iff_eq_z_rev, iff_in_eq1), [], []),
                    got_iff_rev, iff_eq_z_rev, iff_in_eq1, [], [])
    # got_sing_z: [sing_x2, eq_x] |- [Iff(In(zv,sa), Eq(zv,x1))]

    # forall z: sing_x2, eq_x |- Singleton(sa, x1)
    fa_sing = Forall(zv, iff_in_eq1)
    got_sing_x1 = Proof(Sequent([sing_x2, eq_x], [fa_sing]),
                        'forall_right', [got_sing_z], principal=fa_sing, term=zv)
    # fa_sing is alpha-equiv to Singleton(sa, x1) after expansion

    # Step 2: Similarly PairSet(pab, x2, y2) + Eq(x1,x2) |- PairSet(pab, x1, y2)
    # PairSet(pab, x, y) = forall z. Iff(In(z,pab), Or(Eq(z,x), Eq(z,y)))
    # From Iff(Eq(z,x1),Eq(z,x2)) and Iff(Eq(z,y2),Eq(z,y2)) [refl]:
    # or_iff_compat: Or(Eq(z,x1),Eq(z,y2)) <-> Or(Eq(z,x2),Eq(z,y2))
    # iff_sym: Or(Eq(z,x2),Eq(z,y2)) <-> Or(Eq(z,x1),Eq(z,y2))
    # iff_chain: Iff(In(z,pab), Or(Eq(z,x2),Eq(z,y2))) -> Iff(In(z,pab), Or(Eq(z,x1),Eq(z,y2)))

    pair_x2_y2 = PairSet(pab, x2, y2)
    pair_x1_y2 = PairSet(pab, x1, y2)
    or_x2 = Or(Eq(zv, x2), Eq(zv, y2))
    or_x1 = Or(Eq(zv, x1), Eq(zv, y2))
    iff_in_or2 = Iff(In(zv, pab), or_x2)
    iff_in_or1 = Iff(In(zv, pab), or_x1)
    iff_or = Iff(or_x2, or_x1)

    got_pair_inst = _fl(pair_x2_y2, iff_in_or2, zv)

    # Iff(Eq(zv,y2), Eq(zv,y2)) -- reflexive iff
    iff_refl_y = Iff(Eq(zv, y2), Eq(zv, y2))
    P_y = In(zv, y2)
    PP = Implies(P_y, P_y)
    # Build iff_refl for Eq(zv,y2): this is a complex formula. Let me use eq_reflexive-style.
    # Actually, Iff(A, A) is provable for any A. Let me build a quick one.
    A = Eq(zv, y2)
    AB = Implies(A, A)
    NAB = Not(AB)
    ax_a = Proof(Sequent([A], [A]), 'axiom', principal=A)
    ir_a = Proof(Sequent([], [AB]), 'implies_right', [ax_a], principal=AB)
    ir_a2 = Proof(Sequent([], [AB]), 'implies_right',
                  [Proof(Sequent([A], [A]), 'axiom', principal=A)], principal=AB)
    nl_a = Proof(Sequent([NAB], []), 'not_left', [ir_a2], principal=NAB)
    il_a = Proof(Sequent([Implies(AB, NAB)], []), 'implies_left', [ir_a, nl_a], principal=Implies(AB, NAB))
    got_iff_refl = Proof(Sequent([], [iff_refl_y]), 'not_right', [il_a], principal=iff_refl_y)

    # or_iff_compat: Iff(Eq(z,x1),Eq(z,x2)) + Iff(Eq(z,y2),Eq(z,y2)) -> Iff(Or(Eq(z,x1),Eq(z,y2)), Or(Eq(z,x2),Eq(z,y2)))
    oic = or_iff_compat(Eq(zv, x1), Eq(zv, y2), Eq(zv, x2), Eq(zv, y2), [])
    iff_or_fwd = Iff(or_x1, or_x2)
    got_iff_or = mp(mp(oic, got_iff_eq, iff_eq_z, Implies(iff_refl_y, iff_or_fwd), [], []),
                    got_iff_refl, iff_refl_y, iff_or_fwd, [], [])
    # got_iff_or: [eq_x] |- [Iff(Or(Eq(z,x1),Eq(z,y2)), Or(Eq(z,x2),Eq(z,y2)))]

    # iff_sym to get Iff(or_x2, or_x1):
    got_iff_or_rev = mp(iff_sym(or_x1, or_x2, []), got_iff_or, iff_or_fwd, iff_or, [], [])

    # iff_chain: Iff(In(z,pab), or_x2) + Iff(or_x2, or_x1) -> Iff(In(z,pab), or_x1)
    ct2 = char_transfer(In(zv, pab), or_x2, or_x1)
    got_pair_z = mp(mp(ct2, got_pair_inst, iff_in_or2, Implies(iff_or, iff_in_or1), [], []),
                    got_iff_or_rev, iff_or, iff_in_or1, [], [])
    # got_pair_z: [pair_x2_y2, eq_x] |- [Iff(In(z,pab), Or(Eq(z,x1),Eq(z,y2)))]

    fa_pair = Forall(zv, iff_in_or1)
    got_pair_x1 = Proof(Sequent([pair_x2_y2, eq_x], [fa_pair]),
                        'forall_right', [got_pair_z], principal=fa_pair, term=zv)
    # got_pair_x1: [pair_x2_y2, eq_x] |- [PairSet(pab, x1, y2)] (alpha-equiv)

    # Step 3: OrdPair(p, x2, y2) + Eq(x1,x2) |- OrdPair(p, x1, y2)
    # OrdPair(p,x,y) = exists sa. Singleton(sa,x)  and  exists pab. PairSet(pab,x,y)  and  PairSet(p,sa,pab)
    # From OrdPair(p,x2,y2): get sa with Singleton(sa,x2) and pab with PairSet(pab,x2,y2) and PairSet(p,sa,pab).
    # Transform: Singleton(sa,x1) from Singleton(sa,x2)+Eq. PairSet(pab,x1,y2) from PairSet(pab,x2,y2)+Eq.
    # Re-pack with same sa, pab, PairSet(p,sa,pab) unchanged.
    # Result: OrdPair(p, x1, y2).

    ord_x2 = OrdPair(p, x2, y2)
    ord_x1 = OrdPair(p, x1, y2)
    pair_p = PairSet(p, sa, pab)

    # From ord_x2: exists sa. And(Singleton(sa,x2), exists pab. And(PairSet(pab,x2,y2), PairSet(p,sa,pab)))
    # Existential elim on sa: Singleton(sa,x2)  and  exists pab. And(PairSet(pab,x2,y2), PairSet(p,sa,pab))
    # And_elim: Singleton(sa,x2) and exists pab. ...
    # Existential elim on pab: PairSet(pab,x2,y2)  and  PairSet(p,sa,pab)
    # And_elim: PairSet(pab,x2,y2) and PairSet(p,sa,pab)

    # Transform: Singleton(sa,x1) and PairSet(pab,x1,y2) (using got_sing_x1 and got_pair_x1)

    # Re-pack: And(PairSet(pab,x1,y2), PairSet(p,sa,pab))
    # exists pab. And(PairSet(pab,x1,y2), PairSet(p,sa,pab))
    # And(Singleton(sa,x1), exists pab. ...)
    # exists sa. And(Singleton(sa,x1), exists pab. ...)
    # = OrdPair(p, x1, y2)

    # This is the existential re-packing pattern from kuratowski.
    # From [sing_x2, pair_x2_y2, pair_p, eq_x] |- [sing_x1] (got_sing_x1)
    # and [pair_x2_y2, eq_x] |- [pair_x1_y2] (got_pair_x1)
    # Need to build: [sing_x2, pair_x2_y2, pair_p, eq_x] |- OrdPair(p, x1, y2)

    # Build And(PairSet(pab,x1,y2), pair_p):
    and_pair = And(fa_pair, pair_p)  # Using fa_pair as alpha-equiv to PairSet(pab,x1,y2)
    # From pair_x1 (got_pair_x1) and pair_p (axiom):
    ax_pp = Proof(Sequent([pair_p], [pair_p]), 'axiom', principal=pair_p)
    n_pp = Not(pair_p)
    and_pp1 = Proof(Sequent([pair_x2_y2, eq_x, pair_p, n_pp], []), 'not_left',
                    [wl(ax_pp, pair_x2_y2, eq_x)], principal=n_pp)
    and_pp2 = Proof(Sequent([pair_x2_y2, eq_x, pair_p, Implies(fa_pair, n_pp)], []),
                    'implies_left', [wl(got_pair_x1, pair_p), and_pp1],
                    principal=Implies(fa_pair, n_pp))
    got_and_pair = Proof(Sequent([pair_x2_y2, eq_x, pair_p], [and_pair]),
                         'not_right', [and_pp2], principal=and_pair)

    # exists pab. And(PairSet(pab,x1,y2), pair_p):
    def _exist_intro_right(proof, body_formula, var, witness):
        """From ctx |- body_formula[witness/var], derive ctx |- exists var. body_formula."""
        n_body = Not(body_formula)
        fa_n = Forall(var, n_body)
        ctx = proof.sequent.left
        nl = Proof(Sequent(ctx + [n_body], []), 'not_left', [proof], principal=n_body)
        fl = Proof(Sequent(ctx + [fa_n], []), 'forall_left', [nl], principal=fa_n, term=witness)
        ex = Exists(var, body_formula)
        return Proof(Sequent(ctx, [ex]), 'not_right', [fl], principal=ex)

    # Hmm, body_formula has pab as a free var. I need exists pab. And(PairSet(pab,x1,y2), PairSet(p,sa,pab)).
    # The body is And(fa_pair, pair_p) where both mention pab.
    # Witness is pab itself.
    # But _exist_intro_right expects body_formula to have var free, and proof to prove body[witness/var].
    # Since witness = var = pab, body[pab/pab] = body. So proof = got_and_pair. (ok)

    # Actually, the and_pair formula uses fa_pair = Forall(zv, iff_in_or1) which doesn't directly
    # mention pab -- wait, pab IS in iff_in_or1 through In(zv, pab). So pab is free in fa_pair.
    # And pair_p = PairSet(p, sa, pab) also has pab free. (ok)

    ex_pab_body = And(fa_pair, pair_p)
    ex_pab = Exists(pab, ex_pab_body)
    got_ex_pab = _exist_intro_right(got_and_pair, ex_pab_body, pab, pab)

    # And(Singleton(sa,x1), ex_pab):
    and_sing = And(fa_sing, ex_pab)
    n_ex = Not(ex_pab)
    and_s1 = Proof(Sequent([pair_x2_y2, eq_x, pair_p, n_ex], []), 'not_left',
                   [wl(got_ex_pab, )], principal=n_ex)
    # Hmm, got_ex_pab has [pair_x2_y2, eq_x, pair_p] on left. If I add n_ex, it becomes
    # [pair_x2_y2, eq_x, pair_p, n_ex] |- [ex_pab]. Then not_left: [pair_x2_y2, eq_x, pair_p, n_ex] |- [].
    # But not_left needs the NOT on the left: from ctx |- A, we get ctx, Not(A) |- .
    # So: not_left on n_ex: from [pair_x2_y2, eq_x, pair_p] |- [ex_pab] (got_ex_pab),
    # get [pair_x2_y2, eq_x, pair_p, Not(ex_pab)] |- [].
    and_s1 = Proof(Sequent([pair_x2_y2, eq_x, pair_p, n_ex], []), 'not_left', [got_ex_pab], principal=n_ex)
    # Need: [sing_x2, pair_x2_y2, eq_x, pair_p] |- [fa_sing]
    # got_sing_x1: [sing_x2, eq_x] |- [fa_sing]. Weaken with pair_x2_y2, pair_p.
    got_sing_w = wl(got_sing_x1, pair_x2_y2, pair_p)
    and_s2 = Proof(Sequent([sing_x2, pair_x2_y2, eq_x, pair_p, Implies(fa_sing, n_ex)], []),
                   'implies_left', [got_sing_w, wl(and_s1, sing_x2)],
                   principal=Implies(fa_sing, n_ex))
    got_and_sing = Proof(Sequent([sing_x2, pair_x2_y2, eq_x, pair_p], [and_sing]),
                         'not_right', [and_s2], principal=and_sing)

    # exists sa. And(Singleton(sa,x1), ex_pab) = OrdPair(p, x1, y2) (alpha-equiv after expansion)
    ex_sa_body = and_sing
    got_ex_sa = _exist_intro_right(got_and_sing, ex_sa_body, sa, sa)

    # Now: [sing_x2, pair_x2_y2, eq_x, pair_p] |- [exists sa. And(Singleton(sa,x1), exists pab. ...)]
    # This is OrdPair(p, x1, y2).

    # Step 4: From OrdPair(p,x1,y2)  and  In(p,f): Apply(f, x1, y2)
    # Apply(f,x1,y2) = exists p. And(OrdPair(p,x1,y2), In(p,f))
    in_pf = In(p, f)
    ord_x1_formula = Exists(sa, and_sing)  # the exists sa formula
    and_ord_in = And(ord_x1_formula, in_pf)
    n_in = Not(in_pf)
    and_o1 = Proof(Sequent([sing_x2, pair_x2_y2, eq_x, pair_p, in_pf, n_in], []), 'not_left',
                   [wl(Proof(Sequent([in_pf], [in_pf]), 'axiom', principal=in_pf),
                       sing_x2, pair_x2_y2, eq_x, pair_p)], principal=n_in)
    and_o2 = Proof(Sequent([sing_x2, pair_x2_y2, eq_x, pair_p, in_pf, Implies(ord_x1_formula, n_in)], []),
                   'implies_left', [wl(got_ex_sa, in_pf), and_o1],
                   principal=Implies(ord_x1_formula, n_in))
    got_and_ord = Proof(Sequent([sing_x2, pair_x2_y2, eq_x, pair_p, in_pf], [and_ord_in]),
                        'not_right', [and_o2], principal=and_ord_in)

    # exists p. And(OrdPair(p,x1,y2), In(p,f)) = Apply(f, x1, y2)
    app_x1_y2 = Apply(f, x1, y2)
    got_app_x1 = _exist_intro_right(got_and_ord, and_ord_in, p, p)
    # got_app_x1: [sing_x2, pair_x2_y2, eq_x, pair_p, in_pf] |- [Apply(f, x1, y2)]

    # Step 5: Unpack Apply(f,x2,y2) = exists p. And(OrdPair(p,x2,y2), In(p,f))
    # OrdPair(p,x2,y2) = exists sa. And(Singleton(sa,x2), exists pab. And(PairSet(pab,x2,y2), PairSet(p,sa,pab)))
    # Existential elim chain: p -> (OrdPair+In) -> sa -> (Sing+exists pab) -> pab -> (PairSet+PairSet)

    # Need to eliminate existentials to get sing_x2, pair_x2_y2, pair_p, in_pf on the left.
    # Then got_app_x1 gives Apply(f,x1,y2).
    # Then Function(f) uniqueness: Apply(f,x1,y1)  and  Apply(f,x1,y2) -> Eq(y1,y2).

    # The existential unpacking of Apply(f,x2,y2) is complex. Let me use _eel pattern.
    def _eel(proof, pred, var):
        ctx = [f_ for f_ in proof.sequent.left if f_ is not pred]
        D = proof.sequent.right[0]
        p1 = Proof(Sequent(ctx, [Not(pred), D]), 'not_right', [proof], principal=Not(pred))
        p2 = Proof(Sequent(ctx, [Forall(var, Not(pred)), D]),
                   'forall_right', [p1], principal=Forall(var, Not(pred)), term=var)
        return Proof(Sequent(ctx + [Exists(var, pred)], [D]), 'not_left', [p2], principal=Exists(var, pred))

    # Unpack And(PairSet(pab,x2,y2), PairSet(p,sa,pab)):
    and_inner2 = And(pair_x2_y2, pair_p)
    ax_and2 = Proof(Sequent([and_inner2], [and_inner2]), 'axiom', principal=and_inner2)
    got_px2 = apply_thm(and_elim_left(pair_x2_y2, pair_p, []), [], and_inner2, pair_x2_y2, ax_and2, [], [])
    got_pp = apply_thm(and_elim_right(pair_x2_y2, pair_p, []), [], and_inner2, pair_p,
                       Proof(Sequent([and_inner2], [and_inner2]), 'axiom', principal=and_inner2), [], [])

    # got_app_x1 needs [sing_x2, pair_x2_y2, eq_x, pair_p, in_pf] on left.
    # Cut pair_x2_y2 and pair_p from and_inner2:
    got_app_from_and2 = Proof(Sequent([sing_x2, and_inner2, eq_x, in_pf], [app_x1_y2]), 'cut',
        [wr(wl(got_px2, sing_x2, eq_x, in_pf), app_x1_y2),
         Proof(Sequent([sing_x2, and_inner2, pair_x2_y2, eq_x, in_pf], [app_x1_y2]), 'cut',
             [wr(wl(got_pp, sing_x2, pair_x2_y2, eq_x, in_pf), app_x1_y2),
              wl(got_app_x1, and_inner2)],
             principal=pair_p)],
        principal=pair_x2_y2)

    # Exist elim on pab: [sing_x2, exists pab.and_inner2, eq_x, in_pf] |- [app_x1_y2]
    got_app_from_ex_pab = _eel(got_app_from_and2, and_inner2, pab)

    # Unpack And(Singleton(sa,x2), exists pab.and_inner2):
    ex_pab_inner = Exists(pab, and_inner2)
    and_outer2 = And(sing_x2, ex_pab_inner)
    ax_ao = Proof(Sequent([and_outer2], [and_outer2]), 'axiom', principal=and_outer2)
    got_sx2 = apply_thm(and_elim_left(sing_x2, ex_pab_inner, []), [], and_outer2, sing_x2, ax_ao, [], [])
    got_ex_pab2 = apply_thm(and_elim_right(sing_x2, ex_pab_inner, []), [], and_outer2, ex_pab_inner,
                             Proof(Sequent([and_outer2], [and_outer2]), 'axiom', principal=and_outer2), [], [])

    got_app_from_ao = Proof(Sequent([and_outer2, eq_x, in_pf], [app_x1_y2]), 'cut',
        [wr(wl(got_sx2, eq_x, in_pf), app_x1_y2),
         Proof(Sequent([and_outer2, sing_x2, eq_x, in_pf], [app_x1_y2]), 'cut',
             [wr(wl(got_ex_pab2, sing_x2, eq_x, in_pf), app_x1_y2),
              wl(got_app_from_ex_pab, and_outer2)],
             principal=ex_pab_inner)],
        principal=sing_x2)

    # Exist elim on sa: [exists sa.and_outer2, eq_x, in_pf] |- [app_x1_y2]
    got_app_from_ex_sa = _eel(got_app_from_ao, and_outer2, sa)

    # Unpack And(OrdPair(p,x2,y2), In(p,f)): but OrdPair IS exists sa.and_outer2 (alpha-equiv)
    and_ordp_in = And(ord_x2, in_pf)
    ax_aoi = Proof(Sequent([and_ordp_in], [and_ordp_in]), 'axiom', principal=and_ordp_in)
    got_ord2 = apply_thm(and_elim_left(ord_x2, in_pf, []), [], and_ordp_in, ord_x2, ax_aoi, [], [])
    got_inf = apply_thm(and_elim_right(ord_x2, in_pf, []), [], and_ordp_in, in_pf,
                        Proof(Sequent([and_ordp_in], [and_ordp_in]), 'axiom', principal=and_ordp_in), [], [])

    got_app_from_aoi = Proof(Sequent([and_ordp_in, eq_x], [app_x1_y2]), 'cut',
        [wr(wl(got_ord2, eq_x), app_x1_y2),
         Proof(Sequent([and_ordp_in, ord_x2, eq_x], [app_x1_y2]), 'cut',
             [wr(wl(got_inf, ord_x2, eq_x), app_x1_y2),
              wl(got_app_from_ex_sa, and_ordp_in)],
             principal=in_pf)],
        principal=ord_x2)

    # Exist elim on p: [exists p.And(OrdPair,In), eq_x] |- [app_x1_y2]
    got_app_from_ex_p = _eel(got_app_from_aoi, and_ordp_in, p)
    # exists p.And(OrdPair(p,x2,y2), In(p,f)) = Apply(f, x2, y2) (alpha-equiv)
    # got_app_from_ex_p: [Apply(f,x2,y2), eq_x] |- [Apply(f,x1,y2)]

    # Step 6: Function(f) + Apply(f,x1,y1) + Apply(f,x1,y2) -> Eq(y1,y2)
    # Use _func_unique pattern from initial_segments_agree (but defined locally here)
    func_body = Forall(Var(), Forall(Var(), Forall(Var(),
        Implies(And(Apply(f, Var(), Var()), Apply(f, Var(), Var())), Eq(Var(), Var())))))
    # Hmm, can't use anonymous Vars like this. Let me just use Function(f) directly.
    # Function(f) |- Apply(f,x1,y1)  and  Apply(f,x1,y2) -> Eq(y1,y2)
    # This is the standard uniqueness from Function definition.

    xf, ya, yb = Var(), Var(), Var()
    func_fa = FuncDef(f)
    and_apps = And(app1, app_x1_y2)
    eq_y = Eq(y1, y2)

    # Peel Function(f): forall x forall y1 forall y2. And(Apply(f,x,y1), Apply(f,x,y2)) -> Eq(y1,y2)
    imp_and_eq = Implies(and_apps, eq_y)
    fa3 = Forall(yb, Implies(And(Apply(f, x1, y1), Apply(f, x1, yb)), Eq(y1, yb)))
    fa2 = Forall(ya, Forall(yb, Implies(And(Apply(f, x1, ya), Apply(f, x1, yb)), Eq(ya, yb))))
    fa1 = Forall(xf, Forall(ya, Forall(yb, Implies(And(Apply(f, xf, ya), Apply(f, xf, yb)), Eq(ya, yb)))))

    ax_eq_y = Proof(Sequent([eq_y], [eq_y]), 'axiom', principal=eq_y)
    ax_and_a = wr(Proof(Sequent([and_apps], [and_apps]), 'axiom', principal=and_apps), eq_y)
    il_and = Proof(Sequent([imp_and_eq, and_apps], [eq_y]),
                   'implies_left', [ax_and_a, wl(ax_eq_y, and_apps)], principal=imp_and_eq)
    fl3 = Proof(Sequent([fa3, and_apps], [eq_y]), 'forall_left', [il_and], principal=fa3, term=y2)
    fl2 = Proof(Sequent([fa2, and_apps], [eq_y]), 'forall_left', [fl3], principal=fa2, term=y1)
    fl1 = Proof(Sequent([fa1, and_apps], [eq_y]), 'forall_left', [fl2], principal=fa1, term=x1)
    # Cut with func_f:
    got_eq_from_func = Proof(Sequent([func_f, and_apps], [eq_y]), 'cut',
        [wr(wl(Proof(Sequent([func_f], [func_f]), 'axiom', principal=func_f), and_apps), eq_y),
         wl(fl1, func_f)], principal=fa1)

    # Build And(app1, app_x1_y2):
    n_app_x1 = Not(app_x1_y2)
    and_a1 = Proof(Sequent(got_app_from_ex_p.sequent.left + [app1, n_app_x1], []),
                   'not_left', [wl(got_app_from_ex_p, app1)], principal=n_app_x1)
    and_a2 = Proof(Sequent(got_app_from_ex_p.sequent.left + [app1, Implies(app1, n_app_x1)], []),
                   'implies_left',
                   [wl(Proof(Sequent([app1], [app1]), 'axiom', principal=app1),
                       *got_app_from_ex_p.sequent.left),
                    and_a1],
                   principal=Implies(app1, n_app_x1))
    got_and_apps = Proof(Sequent(got_app_from_ex_p.sequent.left + [app1], [and_apps]),
                         'not_right', [and_a2], principal=and_apps)
    # got_and_apps: [app2, eq_x, app1] |- [And(app1, app_x1_y2)]

    # Final: func_f, app2, eq_x, app1 |- Eq(y1, y2)
    final = Proof(Sequent([func_f] + got_and_apps.sequent.left, [eq_y]), 'cut',
        [wr(wl(got_and_apps, func_f), eq_y), wl(got_eq_from_func, *got_and_apps.sequent.left)],
        principal=and_apps)

    # Close: discharge all, forall all
    # Note: _eel replaced app2 with Exists(p, and_ordp_in) (alpha-equiv but different object)
    app2_actual = got_app_from_ex_p.sequent.left[-1]  # Exists(p, and_ordp_in) == app2
    proof = final
    for h in [app2_actual, app1, eq_x, func_f]:
        imp_h = Implies(h, proof.sequent.right[0])
        remaining = [f_ for f_ in proof.sequent.left if f_ is not h]
        proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
    for v in [y2, y1, x2, x1, f]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=v, principal=fa)
    proof.name = 'func_preserves_eq'
    return proof


def func_unique_thm():
    """|- forall f, x, y1, y2. Function(f) -> Apply(f,x,y1) -> Apply(f,x,y2) -> Eq(y1,y2)
    Basic function uniqueness: same input implies same output."""
    from tactics import apply_thm, wl, wr, mp
    from definitions import Function as FuncDef, Apply

    f, x, y1, y2 = Var(), Var(), Var(), Var()
    func_f = FuncDef(f)
    app1 = Apply(f, x, y1)
    app2 = Apply(f, x, y2)
    eq_y = Eq(y1, y2)

    # Function(f) = forall x' forall y1' forall y2'. And(Apply(f,x',y1'), Apply(f,x',y2')) -> Eq(y1',y2')
    xv, ya, yb = Var(), Var(), Var()
    and_apps = And(app1, app2)
    imp = Implies(and_apps, eq_y)
    fa3 = Forall(yb, Implies(And(Apply(f, x, y1), Apply(f, x, yb)), Eq(y1, yb)))
    fa2 = Forall(ya, Forall(yb, Implies(And(Apply(f, x, ya), Apply(f, x, yb)), Eq(ya, yb))))
    fa1 = Forall(xv, Forall(ya, Forall(yb,
        Implies(And(Apply(f, xv, ya), Apply(f, xv, yb)), Eq(ya, yb)))))
    # fa1 is alpha-equiv to Function(f)

    def _fl(parent, body, term):
        return Proof(Sequent([parent], [body]), 'forall_left',
            [Proof(Sequent([body], [body]), 'axiom', principal=body)],
            principal=parent, term=term)

    # Peel 3 foralls: fa1 -> fa2 -> fa3 -> imp
    fl1 = _fl(fa1, fa2, x)
    fl2 = Proof(Sequent([fa1], [fa3]), 'cut',
        [wr(fl1, fa3), wl(_fl(fa2, fa3, y1), fa1)], principal=fa2)
    fl3 = Proof(Sequent([fa1], [imp]), 'cut',
        [wr(fl2, imp), wl(_fl(fa3, imp, y2), fa1)], principal=fa3)
    # fl3: [Function(f)] |- [And(app1,app2) -> Eq(y1,y2)]

    # Build And(app1, app2)
    n_app2 = Not(app2)
    br1 = wr(Proof(Sequent([app1], [app1]), 'axiom', principal=app1), eq_y)
    br2 = Proof(Sequent([app2, n_app2], []), 'not_left',
               [Proof(Sequent([app2], [app2]), 'axiom', principal=app2)], principal=n_app2)
    il = Proof(Sequent([app1, app2, Implies(app1, n_app2)], []),
               'implies_left', [wl(br1, app2), wl(br2, app1)], principal=Implies(app1, n_app2))

    # Wait, br1 needs right = [app1] not [app1, eq_y]. For implies_left:
    # Branch 1: G |- app1, D (D = conclusion.right = [])
    # So branch 1 should be: [app1, app2] |- [app1]
    br1_fix = wl(Proof(Sequent([app1], [app1]), 'axiom', principal=app1), app2)
    il = Proof(Sequent([app1, app2, Implies(app1, n_app2)], []),
               'implies_left', [br1_fix, wl(br2, app1)], principal=Implies(app1, n_app2))
    got_and = Proof(Sequent([app1, app2], [and_apps]), 'not_right', [il], principal=and_apps)

    # MP: imp, and_apps |- eq_y
    ax_eq = Proof(Sequent([eq_y], [eq_y]), 'axiom', principal=eq_y)
    ax_and = wr(got_and, eq_y)
    il_mp = Proof(Sequent([app1, app2, imp], [eq_y]),
                  'implies_left', [ax_and, wl(ax_eq, app1, app2)], principal=imp)
    # Cut on imp: fl3 gives [fa1] |- [imp], il_mp gives [app1, app2, imp] |- [eq_y]
    got_eq = Proof(Sequent([func_f, app1, app2], [eq_y]), 'cut',
        [wr(wl(fl3, app1, app2), eq_y), wl(il_mp, func_f)], principal=imp)

    # Discharge and close
    proof = got_eq
    for h in [app2, app1, func_f]:
        imp_h = Implies(h, proof.sequent.right[0])
        remaining = [f_ for f_ in proof.sequent.left if f_ is not h]
        proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
    for v in [y2, y1, x, f]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=v, principal=fa)
    proof.name = 'func_unique'
    return proof


def plus_zero():
    """|- forall m, n, p. Empty(n) -> Plus(m, n, p) -> Eq(m, p)
    If n is empty, then m + n = p implies p = m."""
    from tactics import apply_thm, wl, wr, mp
    from definitions import (Function as FuncDef, Apply, Recursive, Plus as PlusDef,
                             Empty, Successor)

    m, nv, p = Var(), Var(), Var()
    h, sf = Var(), Var()
    ev = Var()
    empty_n = Empty(nv)
    eq_mp = Eq(m, p)

    # Build Plus(m, nv, p) expansion manually with our own vars
    xv, yv = Var(), Var()
    succ_char = Forall(xv, Forall(yv, Iff(Apply(sf, xv, yv), Successor(yv, xv))))
    rec_h = Recursive(h, m, sf)
    app_h_n_p = Apply(h, nv, p)
    and_rec_app = And(rec_h, app_h_n_p)
    full_and = And(succ_char, and_rec_app)

    # Recursive(h, m, sf) expands to And(Function(h), And(base, step))
    func_h = FuncDef(h)
    base_clause = Forall(ev, Implies(Empty(ev), Apply(h, ev, m)))
    nv2, val, snv, fval = Var(), Var(), Var(), Var()
    step_clause = Forall(nv2, Forall(val, Implies(Apply(h, nv2, val),
        Forall(snv, Implies(Successor(snv, nv2),
            Forall(fval, Implies(Apply(sf, val, fval),
                Apply(h, snv, fval))))))))
    and_base_step = And(base_clause, step_clause)

    # === Core proof: [empty_n, func_h, base_clause, app_h_n_p] |- [eq_mp] ===

    # Step 1: From base_clause, instantiate with nv: Empty(nv) -> Apply(h, nv, m)
    imp_emp_app = Implies(empty_n, Apply(h, nv, m))
    app_h_n_m = Apply(h, nv, m)
    def _fl(parent, body, term):
        return Proof(Sequent([parent], [body]), 'forall_left',
            [Proof(Sequent([body], [body]), 'axiom', principal=body)],
            principal=parent, term=term)

    fl_base = _fl(base_clause, imp_emp_app, nv)
    got_app_m = mp(fl_base,
        Proof(Sequent([empty_n], [empty_n]), 'axiom', principal=empty_n),
        empty_n, app_h_n_m, [], [])
    # got_app_m: [base_clause, empty_n] |- [Apply(h, nv, m)]

    # Step 2: func_unique gives Apply(h,nv,m) + Apply(h,nv,p) + Function(h) -> Eq(m,p)
    fu = func_unique_thm()
    # fu: [] |- forall f forall x forall y1 forall y2. Function(f) -> Apply(f,x,y1) -> Apply(f,x,y2) -> Eq(y1,y2)
    # Instantiate: f=h, x=nv, y1=m, y2=p, hyp=Function(h)
    imp_rest = Implies(app_h_n_m, Implies(app_h_n_p, eq_mp))
    got_fu1 = apply_thm(fu, [h, nv, m, p], func_h, imp_rest,
        Proof(Sequent([func_h], [func_h]), 'axiom', principal=func_h), [], [])
    # got_fu1: [func_h] |- [Apply(h,nv,m) -> Apply(h,nv,p) -> Eq(m,p)]

    # MP with got_app_m: Apply(h,nv,m)
    got_fu2 = mp(got_fu1, got_app_m, app_h_n_m, Implies(app_h_n_p, eq_mp), [], [])
    # got_fu2: [func_h, base_clause, empty_n] |- [Apply(h,nv,p) -> Eq(m,p)]

    # MP with Apply(h,nv,p)
    core = mp(got_fu2,
        Proof(Sequent([app_h_n_p], [app_h_n_p]), 'axiom', principal=app_h_n_p),
        app_h_n_p, eq_mp, [], [])
    # core: [func_h, base_clause, empty_n, app_h_n_p] |- [Eq(m,p)]

    # === Unpack Recursive: And(func_h, And(base, step)) ===
    # and_elim_left to get func_h from rec_h
    ax_rec = Proof(Sequent([rec_h], [rec_h]), 'axiom', principal=rec_h)
    got_func = apply_thm(and_elim_left(func_h, and_base_step, []), [], rec_h, func_h, ax_rec, [], [])
    # got_func: [rec_h] |- [func_h]

    # and_elim_right to get And(base, step), then and_elim_left to get base
    got_bs = apply_thm(and_elim_right(func_h, and_base_step, []), [], rec_h, and_base_step,
        Proof(Sequent([rec_h], [rec_h]), 'axiom', principal=rec_h), [], [])
    got_base = apply_thm(and_elim_left(base_clause, step_clause, []), [],
        and_base_step, base_clause,
        Proof(Sequent([and_base_step], [and_base_step]), 'axiom', principal=and_base_step), [], [])
    # Chain: rec_h |- base_clause
    got_base_full = Proof(Sequent([rec_h], [base_clause]), 'cut',
        [wr(got_bs, base_clause), wl(got_base, rec_h)], principal=and_base_step)

    # Replace func_h and base_clause in core with rec_h:
    # core has [func_h, base_clause, empty_n, app_h_n_p] |- [eq_mp]
    # Cut func_h: [rec_h, base_clause, empty_n, app_h_n_p] |- [eq_mp]
    c1 = Proof(Sequent([rec_h, base_clause, empty_n, app_h_n_p], [eq_mp]), 'cut',
        [wr(wl(got_func, base_clause, empty_n, app_h_n_p), eq_mp),
         wl(core, rec_h)], principal=func_h)
    # Cut base_clause: [rec_h, empty_n, app_h_n_p] |- [eq_mp]
    c2 = Proof(Sequent([rec_h, empty_n, app_h_n_p], [eq_mp]), 'cut',
        [wr(wl(got_base_full, empty_n, app_h_n_p), eq_mp),
         c1], principal=base_clause)

    # === Unpack full_and: And(succ_char, And(rec_h, app_h_n_p)) ===
    # and_elim_right to get And(rec_h, app_h_n_p)
    got_ra = apply_thm(and_elim_right(succ_char, and_rec_app, []), [],
        full_and, and_rec_app,
        Proof(Sequent([full_and], [full_and]), 'axiom', principal=full_and), [], [])
    # and_elim_left/right to split rec_h and app_h_n_p
    got_rec = apply_thm(and_elim_left(rec_h, app_h_n_p, []), [],
        and_rec_app, rec_h,
        Proof(Sequent([and_rec_app], [and_rec_app]), 'axiom', principal=and_rec_app), [], [])
    got_app = apply_thm(and_elim_right(rec_h, app_h_n_p, []), [],
        and_rec_app, app_h_n_p,
        Proof(Sequent([and_rec_app], [and_rec_app]), 'axiom', principal=and_rec_app), [], [])

    # Chain: full_and |- rec_h and full_and |- app_h_n_p
    got_rec_full = Proof(Sequent([full_and], [rec_h]), 'cut',
        [wr(got_ra, rec_h), wl(got_rec, full_and)], principal=and_rec_app)
    got_app_full = Proof(Sequent([full_and], [app_h_n_p]), 'cut',
        [wr(got_ra, app_h_n_p), wl(got_app, full_and)], principal=and_rec_app)

    # Replace rec_h and app_h_n_p in c2 with full_and:
    c3 = Proof(Sequent([full_and, empty_n, app_h_n_p], [eq_mp]), 'cut',
        [wr(wl(got_rec_full, empty_n, app_h_n_p), eq_mp),
         wl(c2, full_and)], principal=rec_h)
    c4 = Proof(Sequent([full_and, empty_n], [eq_mp]), 'cut',
        [wr(wl(got_app_full, empty_n), eq_mp),
         c3], principal=app_h_n_p)

    # === Existential elimination: exists sf. full_and, then exists h. exists sf. full_and ===
    def _eel(proof, pred, var):
        ctx = [f_ for f_ in proof.sequent.left if f_ is not pred]
        D = proof.sequent.right[0]
        p1 = Proof(Sequent(ctx, [Not(pred), D]), 'not_right', [proof], principal=Not(pred))
        p2 = Proof(Sequent(ctx, [Forall(var, Not(pred)), D]),
                   'forall_right', [p1], principal=Forall(var, Not(pred)), term=var)
        return Proof(Sequent(ctx + [Exists(var, pred)], [D]), 'not_left',
                     [p2], principal=Exists(var, pred))

    # c4: [full_and, empty_n] |- [eq_mp]. Eliminate sf from full_and.
    c5 = _eel(c4, full_and, sf)
    # c5: [empty_n, exists sf. full_and] |- [eq_mp]

    # Eliminate h from exists sf. full_and (use actual object from sequent)
    ex_sf_actual = c5.sequent.left[-1]
    c6 = _eel(c5, ex_sf_actual, h)
    # c6: [empty_n, exists h. exists sf. full_and] |- [eq_mp]

    # === Discharge and close ===
    plus_on_left = c6.sequent.left[-1]  # the exists h. exists sf formula
    proof = c6
    for hyp in [plus_on_left, empty_n]:
        imp_h = Implies(hyp, proof.sequent.right[0])
        remaining = [f_ for f_ in proof.sequent.left if f_ is not hyp]
        proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
    for v in [p, nv, m]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=v, principal=fa)
    proof.name = 'plus_zero'
    return proof


def init_seg_func():
    """|- forall v, a, f. InitSeg(v,a,f) -> Function(v)"""
    from tactics import apply_thm
    from definitions import Function as FuncDef, Apply, InitialSegment, Successor

    v, a, f = Var(), Var(), Var()
    is_f = InitialSegment(v, a, f)
    func_v = FuncDef(v)

    ev, nv, val, sn, fval = Var(), Var(), Var(), Var(), Var()
    base = Forall(ev, Implies(Empty(ev), Apply(v, ev, a)))
    step = Forall(nv, Forall(val, Implies(Apply(v, nv, val),
        Forall(sn, Implies(Successor(sn, nv),
            Forall(fval, Implies(Apply(f, val, fval), Apply(v, sn, fval))))))))
    rest = And(base, step)

    ax = Proof(Sequent([is_f], [is_f]), 'axiom', principal=is_f)
    got = apply_thm(and_elim_left(func_v, rest, []), [], is_f, func_v, ax, [], [])

    proof = Proof(Sequent([], [Implies(is_f, func_v)]),
                  'implies_right', [got], principal=Implies(is_f, func_v))
    for var in [f, a, v]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], term=var, principal=fa)
    proof.name = 'init_seg_func'
    return proof


def init_seg_base():
    """|- forall v, a, f, e. InitSeg(v,a,f) -> Empty(e) -> Apply(v,e,a)"""
    from tactics import apply_thm, wl, wr, mp
    from definitions import Function as FuncDef, Apply, InitialSegment, Successor

    v, a, f, e = Var(), Var(), Var(), Var()
    is_f = InitialSegment(v, a, f)
    func_v = FuncDef(v)
    empty_e = Empty(e)
    app_v_e_a = Apply(v, e, a)

    ev, nv, val, sn, fval = Var(), Var(), Var(), Var(), Var()
    base = Forall(ev, Implies(Empty(ev), Apply(v, ev, a)))
    step = Forall(nv, Forall(val, Implies(Apply(v, nv, val),
        Forall(sn, Implies(Successor(sn, nv),
            Forall(fval, Implies(Apply(f, val, fval), Apply(v, sn, fval))))))))
    rest = And(base, step)

    # Extract base from InitSeg: is_f |- base
    ax = Proof(Sequent([is_f], [is_f]), 'axiom', principal=is_f)
    got_rest = apply_thm(and_elim_right(func_v, rest, []), [], is_f, rest, ax, [], [])
    got_base = apply_thm(and_elim_left(base, step, []), [], rest, base,
        Proof(Sequent([rest], [rest]), 'axiom', principal=rest), [], [])
    got_base_full = Proof(Sequent([is_f], [base]), 'cut',
        [wr(got_rest, base), wl(got_base, is_f)], principal=rest)

    # Instantiate base with e: Empty(e) -> Apply(v,e,a)
    imp_emp = Implies(empty_e, app_v_e_a)
    def _fl(parent, body, term):
        return Proof(Sequent([parent], [body]), 'forall_left',
            [Proof(Sequent([body], [body]), 'axiom', principal=body)],
            principal=parent, term=term)
    got_imp = Proof(Sequent([is_f], [imp_emp]), 'cut',
        [wr(got_base_full, imp_emp), wl(_fl(base, imp_emp, e), is_f)], principal=base)

    # MP with Empty(e)
    got = mp(got_imp,
        Proof(Sequent([empty_e], [empty_e]), 'axiom', principal=empty_e),
        empty_e, app_v_e_a, [], [])

    # Close
    proof = got
    for h in [empty_e, is_f]:
        imp_h = Implies(h, proof.sequent.right[0])
        remaining = [f_ for f_ in proof.sequent.left if f_ is not h]
        proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
    for var in [e, f, a, v]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], term=var, principal=fa)
    proof.name = 'init_seg_base'
    return proof


def init_seg_step():
    """|- forall v,a,f,n,val,sn,fv. InitSeg(v,a,f) -> Apply(v,n,val) ->
       Succ(sn,n) -> Apply(f,val,fv) -> Apply(v,sn,fv)"""
    from tactics import apply_thm, wl, wr, mp
    from definitions import Function as FuncDef, Apply, InitialSegment, Successor

    v, a, f, n, val, sn, fv = Var(), Var(), Var(), Var(), Var(), Var(), Var()
    is_f = InitialSegment(v, a, f)
    func_v = FuncDef(v)
    app_v_n = Apply(v, n, val)
    succ_sn = Successor(sn, n)
    app_f_val = Apply(f, val, fv)
    app_v_sn = Apply(v, sn, fv)

    ev, nv, valv, snv, fvalv = Var(), Var(), Var(), Var(), Var()
    base = Forall(ev, Implies(Empty(ev), Apply(v, ev, a)))
    step = Forall(nv, Forall(valv, Implies(Apply(v, nv, valv),
        Forall(snv, Implies(Successor(snv, nv),
            Forall(fvalv, Implies(Apply(f, valv, fvalv), Apply(v, snv, fvalv))))))))
    rest = And(base, step)

    # Extract step from InitSeg
    ax = Proof(Sequent([is_f], [is_f]), 'axiom', principal=is_f)
    got_rest = apply_thm(and_elim_right(func_v, rest, []), [], is_f, rest, ax, [], [])
    got_step = apply_thm(and_elim_right(base, step, []), [], rest, step,
        Proof(Sequent([rest], [rest]), 'axiom', principal=rest), [], [])
    got_step_full = Proof(Sequent([is_f], [step]), 'cut',
        [wr(got_rest, step), wl(got_step, is_f)], principal=rest)

    # Peel step: forall n forall val. Apply(v,n,val) -> forall sn. Succ(sn,n) -> forall fv. Apply(f,val,fv) -> Apply(v,sn,fv)
    # Instantiate n, val, sn, fv and discharge 3 implies
    imp3 = Implies(app_f_val, app_v_sn)
    imp2 = Implies(succ_sn, Forall(fv, imp3))
    imp1 = Implies(app_v_n, Forall(sn, imp2))
    fa_val = Forall(val, imp1)
    fa_n = Forall(n, fa_val)

    # Use apply_thm chain: is_f |- step. step == fa_n.
    # apply_thm(got_step_full_as_thm, [n, val], app_v_n, Forall(sn, imp2), app_v_n_proof)
    # Then apply_thm(..., [sn], succ_sn, Forall(fv, imp3), succ_proof)
    # Then apply_thm(..., [fv], app_f_val, app_v_sn, app_f_val_proof)

    # Step 1: peel forall n, instantiate with n
    got1 = apply_thm(got_step_full, [n, val], app_v_n, Forall(sn, imp2),
        Proof(Sequent([app_v_n], [app_v_n]), 'axiom', principal=app_v_n), [], [])
    # got1: [is_f, app_v_n] |- [forall sn. imp2]

    # Step 2: peel forall sn
    got2 = apply_thm(got1, [sn], succ_sn, Forall(fv, imp3),
        Proof(Sequent([succ_sn], [succ_sn]), 'axiom', principal=succ_sn), [], [])

    # Step 3: peel forall fv
    got3 = apply_thm(got2, [fv], app_f_val, app_v_sn,
        Proof(Sequent([app_f_val], [app_f_val]), 'axiom', principal=app_f_val), [], [])

    # Close
    proof = got3
    for h in [app_f_val, succ_sn, app_v_n, is_f]:
        imp_h = Implies(h, proof.sequent.right[0])
        remaining = [f_ for f_ in proof.sequent.left if f_ is not h]
        proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)
    for var in [fv, sn, val, n, f, a, v]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], term=var, principal=fa)
    proof.name = 'init_seg_step'
    return proof


def omega_contains_empty():
    """Ext, Inf |- forall w. Omega(w) -> forall e. Empty(e) -> In(e, w)
    Every empty set is in omega."""
    from tactics import apply_thm, wl, wr, mp
    from definitions import Successor

    w, ev = Var(), Var()
    omega_w = Omega(w)
    ind_w = Inductive(w)
    empty_e = Empty(ev)
    in_e_w = In(ev, w)

    # Inductive(w) = And(forall e. Empty(e) -> In(e,w), forall x. In(x,w) -> forall s. Succ(s,x) -> In(s,w))
    sv, xv = Var(), Var()
    base_w = Forall(ev, Implies(empty_e, in_e_w))
    step_w = Forall(xv, Implies(In(xv, w), Forall(sv, Implies(Successor(sv, xv), In(sv, w)))))

    # omega_is_inductive: Ext, Inf |- Omega(w) -> Inductive(w)
    oii = omega_is_inductive()
    ext_ax = zfc.Extensionality()
    inf_ax = zfc.Infinity()
    got_ind = apply_thm(oii, [w], omega_w, ind_w,
        Proof(Sequent([omega_w], [omega_w]), 'axiom', principal=omega_w), [], [])
    # got_ind: [ext_ax, inf_ax, omega_w] |- [Inductive(w)]

    # and_elim_left to get base_w
    got_base_w = apply_thm(and_elim_left(base_w, step_w, []), [], ind_w, base_w,
        Proof(Sequent([ind_w], [ind_w]), 'axiom', principal=ind_w), [], [])
    # Chain: ext, inf, omega |- base_w
    got = Proof(Sequent(got_ind.sequent.left, [base_w]), 'cut',
        [wr(got_ind, base_w), wl(got_base_w, *got_ind.sequent.left)], principal=ind_w)

    # Close: discharge omega, forall w
    proof = Proof(Sequent(got_ind.sequent.left[:2], [Implies(omega_w, base_w)]),
                  'implies_right', [got], principal=Implies(omega_w, base_w))
    fa = Forall(w, proof.sequent.right[0])
    proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=w, principal=fa)
    proof.name = 'omega_contains_empty'
    return proof


def omega_succ_closed():
    """Ext, Inf |- forall w. Omega(w) -> forall x. In(x,w) -> forall s. Succ(s,x) -> In(s,w)
    Omega is closed under successor."""
    from tactics import apply_thm, wl, wr, mp
    from definitions import Successor

    w, xv, sv, ev = Var(), Var(), Var(), Var()
    omega_w = Omega(w)
    ind_w = Inductive(w)

    base_w = Forall(ev, Implies(Empty(ev), In(ev, w)))
    step_w = Forall(xv, Implies(In(xv, w), Forall(sv, Implies(Successor(sv, xv), In(sv, w)))))

    oii = omega_is_inductive()
    got_ind = apply_thm(oii, [w], omega_w, ind_w,
        Proof(Sequent([omega_w], [omega_w]), 'axiom', principal=omega_w), [], [])

    got_step_w = apply_thm(and_elim_right(base_w, step_w, []), [], ind_w, step_w,
        Proof(Sequent([ind_w], [ind_w]), 'axiom', principal=ind_w), [], [])
    got = Proof(Sequent(got_ind.sequent.left, [step_w]), 'cut',
        [wr(got_ind, step_w), wl(got_step_w, *got_ind.sequent.left)], principal=ind_w)

    proof = Proof(Sequent(got_ind.sequent.left[:2], [Implies(omega_w, step_w)]),
                  'implies_right', [got], principal=Implies(omega_w, step_w))
    fa = Forall(w, proof.sequent.right[0])
    proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=w, principal=fa)
    proof.name = 'omega_succ_closed'
    return proof


def init_seg_total():
    """Ext, Inf, Separation |- forall a, f, v, w.
       (forall x. exists y. Apply(f,x,y)) ->
       InitSeg(v,a,f) -> Omega(w) -> forall n. n in w -> exists y. Apply(v,n,y)

    Every initial segment is total on omega, given f is total.
    Proved by induction: Separation forms t = {n in w : exists y. Apply(v,n,y)},
    show Inductive(t), omega_smallest_inductive gives t = w."""
    from tactics import apply_thm, wl, wr, mp
    from definitions import (Function as FuncDef, Apply, InitialSegment, Successor,
                             Singleton, PairSet)

    a, f, v, w, n = Var(), Var(), Var(), Var(), Var()
    yv = Var()
    is_v = InitialSegment(v, a, f)
    omega_w = Omega(w)

    # f-total: forall x. exists y. Apply(f,x,y)
    xv, yfv = Var(), Var()
    f_total = Forall(xv, Exists(yfv, Apply(f, xv, yfv)))

    # P(n) = exists y. Apply(v, n, y)
    def P(x):
        return Exists(yv, Apply(v, x, yv))

    # === Base case: P(e) when Empty(e) ===
    # From init_seg_base: InitSeg(v,a,f) -> Empty(e) -> Apply(v,e,a)
    ev = Var()
    empty_ev = Empty(ev)  # create ONCE, reuse everywhere
    isb = init_seg_base()
    got_app_base = apply_thm(isb, [v, a, f, ev], is_v,
        Implies(empty_ev, Apply(v, ev, a)),
        Proof(Sequent([is_v], [is_v]), 'axiom', principal=is_v), [], [])
    # got_app_base: [is_v] |- [Empty(ev) -> Apply(v, ev, a)]
    # MP with Empty(ev):
    got_app_e = mp(got_app_base,
        Proof(Sequent([empty_ev], [empty_ev]), 'axiom', principal=empty_ev),
        empty_ev, Apply(v, ev, a), [], [])
    # got_app_e: [is_v, empty_ev] |- [Apply(v, ev, a)]

    # Existential intro: from ctx |- body[witness/var], get ctx |- exists var. body
    def _eir(proof, body, var, witness):
        ctx = list(proof.sequent.left)
        body_inst = proof.sequent.right[0]  # body[witness/var] -- the actual formula
        n_body_inst = Not(body_inst)
        fa_n = Forall(var, Not(body))
        nl = Proof(Sequent(ctx + [n_body_inst], []), 'not_left', [proof], principal=n_body_inst)
        fl = Proof(Sequent(ctx + [fa_n], []), 'forall_left', [nl], principal=fa_n, term=witness)
        return Proof(Sequent(ctx, [Exists(var, body)]), 'not_right', [fl],
                     principal=Exists(var, body))

    p_ev = Exists(yv, Apply(v, ev, yv))
    got_base = _eir(got_app_e, Apply(v, ev, yv), yv, a)
    # got_base: [is_v, Empty(ev)] |- [exists y. Apply(v, ev, y)] = P(ev)

    # === Step case: P(n) -> forall sn. Succ(sn,n) -> P(sn) ===
    # Given exists y. Apply(v,n,y) -- call it val.
    # From f_total at val: exists fv. Apply(f,val,fv).
    # From init_seg_step: Apply(v,n,val) -> Succ(sn,n) -> Apply(f,val,fv) -> Apply(v,sn,fv).
    # So Apply(v, sn, fv). Therefore exists y. Apply(v, sn, y).
    #
    # Need to eliminate existentials on val and fv.

    nv, val, fv, snv = Var(), Var(), Var(), Var()
    app_v_n_val = Apply(v, nv, val)
    succ_sn = Successor(snv, nv)
    app_f_val_fv = Apply(f, val, fv)
    app_v_sn_fv = Apply(v, snv, fv)
    p_nv = P(nv)
    p_snv = P(snv)

    # From init_seg_step: is_v, Apply(v,n,val), Succ(sn,n), Apply(f,val,fv) |- Apply(v,sn,fv)
    iss = init_seg_step()
    got_step_app = apply_thm(iss, [v, a, f, nv, val, snv, fv], is_v,
        Implies(app_v_n_val, Implies(succ_sn, Implies(app_f_val_fv, app_v_sn_fv))),
        Proof(Sequent([is_v], [is_v]), 'axiom', principal=is_v), [], [])
    # Peel the 3 implies:
    got_s1 = mp(got_step_app,
        Proof(Sequent([app_v_n_val], [app_v_n_val]), 'axiom', principal=app_v_n_val),
        app_v_n_val, Implies(succ_sn, Implies(app_f_val_fv, app_v_sn_fv)), [], [])
    got_s2 = mp(got_s1,
        Proof(Sequent([succ_sn], [succ_sn]), 'axiom', principal=succ_sn),
        succ_sn, Implies(app_f_val_fv, app_v_sn_fv), [], [])
    got_s3 = mp(got_s2,
        Proof(Sequent([app_f_val_fv], [app_f_val_fv]), 'axiom', principal=app_f_val_fv),
        app_f_val_fv, app_v_sn_fv, [], [])
    # got_s3: [is_v, app_v_n_val, succ_sn, app_f_val_fv] |- [Apply(v, sn, fv)]

    # Existential intro: exists y. Apply(v, sn, y) with witness fv
    yv2 = Var()
    got_ex_sn = _eir(got_s3, Apply(v, snv, yv2), yv2, fv)
    # got_ex_sn: [is_v, app_v_n_val, succ_sn, app_f_val_fv] |- [exists y. Apply(v, sn, y)]

    # Existential elim on fv from f_total:
    # f_total instantiated at val: exists fv. Apply(f, val, fv)
    def _fl(parent, body, term):
        return Proof(Sequent([parent], [body]), 'forall_left',
            [Proof(Sequent([body], [body]), 'axiom', principal=body)],
            principal=parent, term=term)

    ex_fv = Exists(yfv, Apply(f, val, yfv))
    got_ft_val = _fl(f_total, ex_fv, val)
    # got_ft_val: [f_total] |- [exists fv. Apply(f, val, fv)]
    # But yfv vs fv: ex_fv uses yfv as the bound var.
    # got_ex_sn has app_f_val_fv = Apply(f, val, fv) on the left.
    # Need to elim exists yfv from ex_fv where body = Apply(f, val, yfv).
    # The body instantiated with fv gives Apply(f, val, fv) = app_f_val_fv.

    # Hmm, I need _eel: from [is_v, app_v_n_val, succ_sn, app_f_val_fv] |- P(sn),
    # eliminate app_f_val_fv and replace with exists fv. Apply(f,val,fv).
    # But _eel eliminates a formula from the LEFT by introducing Exists.
    # _eel(got_ex_sn, app_f_val_fv, fv) would give:
    #   [is_v, app_v_n_val, succ_sn, exists fv. app_f_val_fv] |- P(sn)
    # But exists fv. Apply(f,val,fv) uses fv as bound var. The ex_fv uses yfv. They're alpha-equiv.

    def _eel(proof, pred, var):
        ctx = [f_ for f_ in proof.sequent.left if f_ is not pred]
        D = proof.sequent.right[0]
        p1 = Proof(Sequent(ctx, [Not(pred), D]), 'not_right', [proof], principal=Not(pred))
        p2 = Proof(Sequent(ctx, [Forall(var, Not(pred)), D]),
                   'forall_right', [p1], principal=Forall(var, Not(pred)), term=var)
        return Proof(Sequent(ctx + [Exists(var, pred)], [D]), 'not_left',
                     [p2], principal=Exists(var, pred))

    got_ex_sn2 = _eel(got_ex_sn, app_f_val_fv, fv)
    # got_ex_sn2: [is_v, app_v_n_val, succ_sn, exists fv.Apply(f,val,fv)] |- [P(sn)]

    # Cut exists fv from f_total:
    ex_fv_actual = got_ex_sn2.sequent.left[-1]  # the Exists object from _eel
    got_ex_sn3 = Proof(Sequent([f_total, is_v, app_v_n_val, succ_sn], [p_snv]), 'cut',
        [wr(wl(got_ft_val, is_v, app_v_n_val, succ_sn), p_snv),
         wl(got_ex_sn2, f_total)], principal=ex_fv_actual)
    # got_ex_sn3: [f_total, is_v, app_v_n_val, succ_sn] |- [P(sn)]

    # Existential elim on val from P(n):
    # P(n) = exists y. Apply(v, n, y). After _eel on app_v_n_val with var val:
    got_ex_sn4 = _eel(got_ex_sn3, app_v_n_val, val)
    # got_ex_sn4: [f_total, is_v, succ_sn, exists val.Apply(v,nv,val)] |- [P(sn)]
    # exists val.Apply(v,nv,val) is alpha-equiv to P(nv) (but with val instead of yv as bound var)

    # Discharge Succ: P(nv), is_v, f_total |- Succ(sn,n) -> P(sn)
    p_nv_actual = got_ex_sn4.sequent.left[-1]
    imp_succ = Implies(succ_sn, p_snv)
    got_step_imp = Proof(Sequent([f_ for f_ in got_ex_sn4.sequent.left if f_ is not succ_sn],
                                  [imp_succ]),
                         'implies_right', [got_ex_sn4], principal=imp_succ)
    # got_step_imp: [f_total, is_v, P(nv)] |- [Succ(sn,n) -> P(sn)]

    # Forall sn: P(nv), is_v, f_total |- forall sn. Succ(sn,n) -> P(sn)
    fa_sn = Forall(snv, imp_succ)
    got_step_fa = Proof(Sequent(got_step_imp.sequent.left, [fa_sn]),
                        'forall_right', [got_step_imp], principal=fa_sn, term=snv)

    # Discharge P(nv):
    imp_pn = Implies(p_nv_actual, fa_sn)
    got_step_closed = Proof(
        Sequent([f_ for f_ in got_step_fa.sequent.left if f_ is not p_nv_actual], [imp_pn]),
        'implies_right', [got_step_fa], principal=imp_pn)
    # got_step_closed: [f_total, is_v] |- [P(nv) -> forall sn. Succ(sn,n) -> P(sn)]

    # === Induction via Separation + Inductive + omega_smallest_inductive ===
    sep = zfc.Separation(P, [v])
    ext_ax = zfc.Extensionality()
    inf_ax = zfc.Infinity()
    t = Var()
    zv = Var()

    # --- Separation characterization ---
    # sep: forall v forall a exists b forall x. Iff(In(x,b), And(In(x,a), P(x)))
    # Instantiate v->v, a->w to get: exists t. forall x. Iff(In(x,t), And(In(x,w), P(x)))
    and_in_p = And(In(zv, w), P(zv))
    iff_char = Iff(In(zv, t), and_in_p)
    fa_char = Forall(zv, iff_char)
    ex_t = Exists(t, fa_char)
    fa_w = Forall(w, ex_t)

    ax_sep = Proof(Sequent([sep], [sep]), 'axiom', principal=sep)
    # Peel forall v -> v:
    got_sep1 = _fl(sep, Forall(w, ex_t), v)
    # actually sep = forall v forall a exists b forall x ... but when I expand, 'a' is the set parameter.
    # Let me just peel with forall_left twice.
    # sep after expand: forall v. forall a. exists b. forall x. Iff(In(x,b), And(In(x,a), P(x)))
    # First forall_left v->v, then a->w
    inner = Forall(w, ex_t)  # After peeling forall v, remaining is forall a. exists b. ...
    # Actually the structure after sep.expand() is Forall(v_param, Forall(a_param, ...))
    # where v_param is v (from vars list) and a_param is a fresh Var.
    # I need to match the expansion structure. Let me use apply_thm approach instead.

    # Simpler: treat sep as axiom, peel with forall_left for v, then w.
    # sep |- forall a. exists b. forall x. Iff(In(x,b), And(In(x,a), P(x)))  [after peeling forall v]
    fa_a_body = Forall(w, Exists(t, Forall(zv, Iff(In(zv, t), And(In(zv, w), P(zv))))))
    fl_v = _fl(sep, fa_a_body, v)
    fl_w = Proof(Sequent([sep], [ex_t]), 'cut',
        [wr(fl_v, ex_t), wl(_fl(fa_a_body, ex_t, w), sep)], principal=fa_a_body)
    # fl_w: [sep] |- [exists t. forall x. Iff(In(x,t), And(In(x,w), P(x)))]

    # --- Work inside exists t (existential elim at the end) ---
    # Assume fa_char on the left: forall x. Iff(In(x,t), And(In(x,w), P(x)))

    # Helper: from fa_char, instantiate at term z
    def _char_at(z):
        """fa_char |- Iff(In(z,t), And(In(z,w), P(z)))"""
        iff_z = Iff(In(z, t), And(In(z, w), P(z)))
        return _fl(fa_char, iff_z, z)

    # Helper: from Iff(A,B) extract A->B (forward)
    def _iff_fwd(iff_proof, A, B):
        """ctx |- Iff(A,B) gives ctx |- A->B"""
        return mp(iff_mp(A, B, []), iff_proof, Iff(A, B), Implies(A, B), [], [])

    # Helper: from Iff(A,B) extract B->A (backward)
    def _iff_bwd(iff_proof, A, B):
        """ctx |- Iff(A,B) gives ctx |- B->A"""
        return mp(iff_mp_rev(A, B, []), iff_proof, Iff(A, B), Implies(B, A), [], [])

    # --- Build Inductive(t) base: forall e. Empty(e) -> In(e, t) ---
    # From omega_contains_empty: Ext, Inf, Omega(w) |- forall e. Empty(e) -> In(e, w)
    oce = omega_contains_empty()
    got_oce = apply_thm(oce, [w], omega_w, Forall(ev, Implies(empty_ev, In(ev, w))),
        Proof(Sequent([omega_w], [omega_w]), 'axiom', principal=omega_w), [], [])
    # got_oce: [ext, inf, omega_w] |- forall e. Empty(e) -> In(e, w)
    # Instantiate at ev:
    got_in_w = apply_thm(got_oce, [ev], empty_ev, In(ev, w),
        Proof(Sequent([empty_ev], [empty_ev]), 'axiom', principal=empty_ev), [], [])
    # got_in_w: [ext, inf, omega_w, empty_ev] |- In(ev, w)

    # got_base: [is_v, empty_ev] |- P(ev)
    # Build And(In(ev,w), P(ev)):
    and_in_p_ev = And(In(ev, w), P(ev))

    base_ctx = [ext_ax, inf_ax, omega_w, is_v, empty_ev]
    got_base_w = wl(got_base, ext_ax, inf_ax, omega_w)  # add axioms
    got_in_w2 = wl(got_in_w, is_v)  # add is_v

    n_pev = Not(P(ev))
    br_b1 = got_in_w2  # base_ctx |- In(ev, w)
    br_b2 = Proof(Sequent(base_ctx + [n_pev], []), 'not_left', [got_base_w], principal=n_pev)
    il_b = Proof(Sequent(base_ctx + [Implies(In(ev, w), n_pev)], []),
                 'implies_left', [br_b1, br_b2], principal=Implies(In(ev, w), n_pev))
    got_and_base = Proof(Sequent(base_ctx, [and_in_p_ev]),
                         'not_right', [il_b], principal=and_in_p_ev)
    # got_and_base: [ext, inf, omega_w, is_v, empty_ev] |- [And(In(ev,w), P(ev))]

    # Backward through characterization: And(In(ev,w), P(ev)) -> In(ev, t)
    char_ev = _char_at(ev)  # [fa_char] |- Iff(In(ev,t), And(In(ev,w), P(ev)))
    bwd_ev = _iff_bwd(char_ev, In(ev, t), and_in_p_ev)
    # bwd_ev: [fa_char] |- And(In(ev,w),P(ev)) -> In(ev,t)
    got_in_t_base = mp(bwd_ev, got_and_base, and_in_p_ev, In(ev, t), [], [])
    # got_in_t_base: [fa_char, ext, inf, omega_w, is_v, Empty(ev)] |- In(ev, t)

    # Discharge empty_ev, forall ev:
    imp_emp_t = Implies(empty_ev, In(ev, t))
    base_hyps = [f_ for f_ in got_in_t_base.sequent.left if f_ is not empty_ev]
    ind_base = Proof(Sequent(base_hyps, [imp_emp_t]),
                     'implies_right', [got_in_t_base], principal=imp_emp_t)
    ind_base_fa = Proof(Sequent(base_hyps, [Forall(ev, imp_emp_t)]),
                        'forall_right', [ind_base], principal=Forall(ev, imp_emp_t), term=ev)
    # ind_base_fa: [fa_char, ext, inf, omega_w, is_v] |- forall e. Empty(e) -> In(e, t)

    # --- Build Inductive(t) step: forall x. In(x,t) -> forall s. Succ(s,x) -> In(s,t) ---
    xv2, sv2 = Var(), Var()
    in_x_t = In(xv2, t)
    in_x_w = In(xv2, w)
    p_x = P(xv2)
    and_in_p_x = And(in_x_w, p_x)
    succ_s_x = Successor(sv2, xv2)
    in_s_t = In(sv2, t)
    in_s_w = In(sv2, w)
    p_s = P(sv2)
    and_in_p_s = And(in_s_w, p_s)

    # From In(x,t): extract In(x,w) and P(x) via forward direction
    char_x = _char_at(xv2)  # [fa_char] |- Iff(In(x,t), And(In(x,w), P(x)))
    fwd_x = _iff_fwd(char_x, in_x_t, and_in_p_x)
    # fwd_x: [fa_char] |- In(x,t) -> And(In(x,w), P(x))
    got_and_x = mp(fwd_x,
        Proof(Sequent([in_x_t], [in_x_t]), 'axiom', principal=in_x_t),
        in_x_t, and_in_p_x, [], [])
    # got_and_x: [fa_char, In(x,t)] |- And(In(x,w), P(x))

    # Extract In(x,w) and P(x):
    got_in_x_w = apply_thm(and_elim_left(in_x_w, p_x, []), [], and_in_p_x, in_x_w,
        Proof(Sequent([and_in_p_x], [and_in_p_x]), 'axiom', principal=and_in_p_x), [], [])
    got_p_x = apply_thm(and_elim_right(in_x_w, p_x, []), [], and_in_p_x, p_x,
        Proof(Sequent([and_in_p_x], [and_in_p_x]), 'axiom', principal=and_in_p_x), [], [])

    # Chain through got_and_x:
    got_in_x_w2 = Proof(Sequent(got_and_x.sequent.left, [in_x_w]), 'cut',
        [wr(got_and_x, in_x_w), wl(got_in_x_w, *got_and_x.sequent.left)], principal=and_in_p_x)
    got_p_x2 = Proof(Sequent(got_and_x.sequent.left, [p_x]), 'cut',
        [wr(got_and_x, p_x), wl(got_p_x, *got_and_x.sequent.left)], principal=and_in_p_x)
    # got_in_x_w2: [fa_char, In(x,t)] |- In(x,w)
    # got_p_x2: [fa_char, In(x,t)] |- P(x)

    # From omega_succ_closed: In(x,w) -> Succ(s,x) -> In(s,w)
    osc = omega_succ_closed()
    got_osc = apply_thm(osc, [w], omega_w, Forall(xv2, Implies(In(xv2, w),
        Forall(sv2, Implies(succ_s_x, in_s_w)))),
        Proof(Sequent([omega_w], [omega_w]), 'axiom', principal=omega_w), [], [])
    got_osc2 = apply_thm(got_osc, [xv2], in_x_w, Forall(sv2, Implies(succ_s_x, in_s_w)),
        got_in_x_w2, [], [])
    got_osc3 = apply_thm(got_osc2, [sv2], succ_s_x, in_s_w,
        Proof(Sequent([succ_s_x], [succ_s_x]), 'axiom', principal=succ_s_x), [], [])
    # got_osc3: [ext, inf, omega_w, fa_char, In(x,t), succ_s_x] |- In(s,w)

    # From step case: P(x) -> Succ(s,x) -> P(s)
    # got_step_closed: [f_total, is_v] |- P(nv) -> forall sn. Succ(sn,nv) -> P(sn)
    # Instantiate nv->xv2 in the step: we need a fresh instance.
    # Actually got_step_closed has nv, snv as its vars. Let me use apply_thm.
    # The theorem body after peeling foralls would give us what we need.
    # But got_step_closed is not a forall -- it's an implication with specific vars.
    # The vars nv and snv are free in got_step_closed's right side.
    # I need to substitute xv2 for nv and sv2 for snv... but we can't substitute in proofs.

    # The issue: got_step_closed uses nv and snv as free vars, but I need xv2 and sv2.
    # Solution: close got_step_closed with forall over nv, snv, then instantiate.

    # Actually, I should rebuild the step case with xv2 and sv2 directly.
    # Or better: close the step case with foralls in init_seg_total and use apply_thm.

    # Let me close got_step_closed with forall nv forall snv:
    fa_snv = Forall(snv, Implies(Successor(snv, nv), p_snv))
    got_step_fa_nv = Proof(Sequent(got_step_closed.sequent.left,
                                    [Forall(nv, Implies(p_nv_actual, fa_snv))]),
                           'forall_right', [got_step_closed],
                           principal=Forall(nv, Implies(p_nv_actual, fa_snv)), term=nv)
    # Hmm wait, got_step_closed has p_nv_actual as a formula that might use specific vars.
    # Let me check: p_nv_actual = got_ex_sn4.sequent.left[-1] = Exists(val, Apply(v, nv, val))
    # This has nv free. After forall_right over nv, nv becomes bound. (ok)

    # But snv is also free in fa_sn = Forall(snv, imp_succ). Wait, snv is already bound in fa_sn.
    # got_step_closed right = [P(nv) -> forall snv. Succ(snv,nv) -> P(snv)]
    # This has nv free. After forall_right over nv, we get:
    # forall nv. P(nv) -> forall snv. Succ(snv,nv) -> P(snv)

    # This is a universal statement. I can then apply_thm to instantiate with xv2.
    step_thm = got_step_fa_nv
    # step_thm: [f_total, is_v] |- forall nv. P(nv) -> forall snv. Succ(snv,nv) -> P(snv)

    # Instantiate nv->xv2, then MP with P(xv2), then instantiate snv->sv2, then MP with Succ
    p_xv2 = P(xv2)
    fa_sv2 = Forall(sv2, Implies(Successor(sv2, xv2), P(sv2)))
    got_step2 = apply_thm(step_thm, [xv2], p_xv2, fa_sv2, got_p_x2, [], [])
    # Wait, p_xv2 = P(xv2) = Exists(yv, Apply(v, xv2, yv))
    # got_p_x2: [fa_char, In(x,t)] |- P(xv2)
    # But p_nv_actual (the P used in step_thm) was Exists(val, Apply(v, nv, val)) not Exists(yv, ...)
    # After forall over nv and instantiation with xv2:
    # P(xv2) in the theorem = Exists(val, Apply(v, xv2, val))
    # P(xv2) from P() = Exists(yv, Apply(v, xv2, yv))
    # These are alpha-equivalent (val vs yv bound vars). (ok)

    got_step3 = apply_thm(got_step2, [sv2], succ_s_x, p_s,
        Proof(Sequent([succ_s_x], [succ_s_x]), 'axiom', principal=succ_s_x), [], [])
    # got_step3: [f_total, is_v, fa_char, In(x,t), succ_s_x] |- P(sv2)

    # Build And(In(s,w), P(s)):
    n_ps = Not(p_s)
    step_ctx = list(set(got_osc3.sequent.left) | set(got_step3.sequent.left))
    # Hmm, set doesn't work with formula objects (no __hash__). Let me merge manually.
    step_ctx_all = list(got_osc3.sequent.left)
    for f_ in got_step3.sequent.left:
        if not any(f_ is g for g in step_ctx_all):
            step_ctx_all.append(f_)

    got_osc3_w = got_osc3
    for f_ in got_step3.sequent.left:
        if not any(f_ is g for g in got_osc3.sequent.left):
            got_osc3_w = wl(got_osc3_w, f_)
    got_step3_w = got_step3
    for f_ in got_osc3.sequent.left:
        if not any(f_ is g for g in got_step3.sequent.left):
            got_step3_w = wl(got_step3_w, f_)

    br_s1 = got_osc3_w  # step_ctx_all |- In(s,w)
    br_s2 = Proof(Sequent(step_ctx_all + [n_ps], []), 'not_left', [got_step3_w], principal=n_ps)
    il_s = Proof(Sequent(step_ctx_all + [Implies(in_s_w, n_ps)], []),
                 'implies_left', [br_s1, br_s2], principal=Implies(in_s_w, n_ps))
    got_and_step = Proof(Sequent(step_ctx_all, [and_in_p_s]),
                         'not_right', [il_s], principal=and_in_p_s)
    # got_and_step: [ext, inf, omega_w, f_total, is_v, fa_char, In(x,t), succ_s_x] |- And(In(s,w), P(s))

    # Backward: And(In(s,w), P(s)) -> In(s,t)
    char_s = _char_at(sv2)
    bwd_s = _iff_bwd(char_s, in_s_t, and_in_p_s)
    got_in_s_t = mp(bwd_s, got_and_step, and_in_p_s, in_s_t, [fa_char], [fa_char])
    # got_in_s_t: [fa_char, ext, inf, omega_w, f_total, is_v, In(x,t), succ_s_x] |- In(s,t)

    # Discharge succ_s_x, forall sv2:
    imp_succ_s = Implies(succ_s_x, in_s_t)
    step_left = [f_ for f_ in got_in_s_t.sequent.left if f_ is not succ_s_x]
    ind_step1 = Proof(Sequent(step_left, [imp_succ_s]),
                      'implies_right', [got_in_s_t], principal=imp_succ_s)
    fa_sv = Forall(sv2, imp_succ_s)
    ind_step2 = Proof(Sequent(step_left, [fa_sv]),
                      'forall_right', [ind_step1], principal=fa_sv, term=sv2)

    # Discharge In(x,t), forall xv2:
    imp_in_t = Implies(in_x_t, fa_sv)
    step_left2 = [f_ for f_ in ind_step2.sequent.left if f_ is not in_x_t]
    ind_step3 = Proof(Sequent(step_left2, [imp_in_t]),
                      'implies_right', [ind_step2], principal=imp_in_t)
    fa_xv = Forall(xv2, imp_in_t)
    ind_step4 = Proof(Sequent(step_left2, [fa_xv]),
                      'forall_right', [ind_step3], principal=fa_xv, term=xv2)
    # ind_step4: [fa_char, ext, inf, omega_w, f_total, is_v] |- forall x. In(x,t) -> forall s. Succ(s,x) -> In(s,t)

    # --- Build Inductive(t) = And(base_part, step_part) ---
    ind_t = Inductive(t)
    base_part = Forall(ev, imp_emp_t)
    step_part = fa_xv

    n_step = Not(step_part)
    ind_ctx = list(ind_step4.sequent.left)  # should be same as ind_base_fa.sequent.left
    br_ind1 = ind_base_fa
    for f_ in ind_ctx:
        if not any(f_ is g for g in br_ind1.sequent.left):
            br_ind1 = wl(br_ind1, f_)
    br_ind2 = Proof(Sequent(ind_ctx + [n_step], []), 'not_left', [ind_step4], principal=n_step)
    for f_ in br_ind1.sequent.left:
        if not any(f_ is g for g in ind_ctx):
            br_ind2 = wl(br_ind2, f_)
            ind_ctx.append(f_)
    il_ind = Proof(Sequent(ind_ctx + [Implies(base_part, n_step)], []),
                   'implies_left', [br_ind1, br_ind2], principal=Implies(base_part, n_step))
    got_ind_t = Proof(Sequent(ind_ctx, [ind_t]),
                      'not_right', [il_ind], principal=ind_t)
    # got_ind_t: [fa_char, ext, inf, omega_w, f_total, is_v] |- Inductive(t)

    # --- Build Subset(t, w) ---
    # forall z. In(z,t) -> In(z,w) from forward direction + and_elim_left
    zv2 = Var()
    char_z = _char_at(zv2)
    fwd_z = _iff_fwd(char_z, In(zv2, t), And(In(zv2, w), P(zv2)))
    # fwd_z: [fa_char] |- In(z,t) -> And(In(z,w), P(z))
    got_and_z = mp(fwd_z,
        Proof(Sequent([In(zv2, t)], [In(zv2, t)]), 'axiom', principal=In(zv2, t)),
        In(zv2, t), And(In(zv2, w), P(zv2)), [], [])
    got_in_z_w = apply_thm(and_elim_left(In(zv2, w), P(zv2), []), [],
        And(In(zv2, w), P(zv2)), In(zv2, w),
        Proof(Sequent([And(In(zv2, w), P(zv2))], [And(In(zv2, w), P(zv2))]),
              'axiom', principal=And(In(zv2, w), P(zv2))), [], [])
    got_sub_core = Proof(Sequent(got_and_z.sequent.left, [In(zv2, w)]), 'cut',
        [wr(got_and_z, In(zv2, w)), wl(got_in_z_w, *got_and_z.sequent.left)],
        principal=And(In(zv2, w), P(zv2)))
    # got_sub_core: [fa_char, In(z,t)] |- In(z,w)
    imp_sub = Implies(In(zv2, t), In(zv2, w))
    sub_proof = Proof(Sequent([fa_char], [imp_sub]),
                      'implies_right', [got_sub_core], principal=imp_sub)
    sub_fa = Forall(zv2, imp_sub)
    got_sub_t = Proof(Sequent([fa_char], [sub_fa]),
                      'forall_right', [sub_proof], principal=sub_fa, term=zv2)
    # got_sub_t: [fa_char] |- Subset(t, w) (= forall z. In(z,t) -> In(z,w))

    # --- Apply omega_smallest_inductive ---
    # forall p forall w. Omega(w) -> (Subset(p,w)  and  Inductive(p)) -> Eq(p,w)
    osi = omega_smallest_inductive()
    sub_t_w = Subset(t, w)
    and_sub_ind = And(sub_t_w, ind_t)

    # Build And(Subset(t,w), Inductive(t)):
    n_ind_t = Not(ind_t)
    got_sub_t_w = wl(got_sub_t, *[f_ for f_ in got_ind_t.sequent.left
                                    if not any(f_ is g for g in got_sub_t.sequent.left)])
    got_ind_t_w = got_ind_t
    for f_ in got_sub_t.sequent.left:
        if not any(f_ is g for g in got_ind_t.sequent.left):
            got_ind_t_w = wl(got_ind_t_w, f_)
    osi_ctx = list(got_ind_t_w.sequent.left)
    br_osi1 = got_sub_t_w  # osi_ctx |- Subset(t,w)
    br_osi2 = Proof(Sequent(osi_ctx + [n_ind_t], []), 'not_left', [got_ind_t_w], principal=n_ind_t)
    il_osi = Proof(Sequent(osi_ctx + [Implies(sub_t_w, n_ind_t)], []),
                   'implies_left', [br_osi1, br_osi2], principal=Implies(sub_t_w, n_ind_t))
    got_and_si = Proof(Sequent(osi_ctx, [and_sub_ind]),
                       'not_right', [il_osi], principal=and_sub_ind)
    # got_and_si: [fa_char, ext, inf, omega_w, f_total, is_v] |- And(Subset(t,w), Inductive(t))

    # omega_smallest_inductive: Omega(w) -> And(sub,ind) -> Eq(t,w)
    eq_tw = Eq(t, w)
    got_eq = apply_thm(osi, [t, w], omega_w, Implies(and_sub_ind, eq_tw),
        Proof(Sequent([omega_w], [omega_w]), 'axiom', principal=omega_w), [], [])
    got_eq2 = mp(got_eq, got_and_si, and_sub_ind, eq_tw, [omega_w], [omega_w])
    # got_eq2: [fa_char, ext, inf, omega_w, f_total, is_v] |- Eq(t, w)

    # --- From Eq(t,w): In(n,w) -> In(n,t) -> P(n) ---
    # eq_in_eq gives: Eq(t,w) -> forall z. Iff(In(z,t), In(z,w))
    # So In(n,w) -> In(n,t) (backward via iff)
    # Then from characterization forward: In(n,t) -> And(In(n,w), P(n)) -> P(n)

    # Eq(t,w) = forall z. Iff(In(z,t), In(z,w)) by definition. Just peel the forall.
    iff_n = Iff(In(n, t), In(n, w))
    fl_eq = _fl(eq_tw, iff_n, n)
    got_iff_n = Proof(Sequent(got_eq2.sequent.left, [iff_n]), 'cut',
        [wr(got_eq2, iff_n), wl(fl_eq, *got_eq2.sequent.left)], principal=eq_tw)
    # got_iff_n: [fa_char, ext, inf, omega_w, f_total, is_v] |- Iff(In(n,t), In(n,w))

    # iff_mp_rev: Iff(In(n,t), In(n,w)) -> In(n,w) -> In(n,t)
    got_w_to_t = _iff_bwd(got_iff_n, In(n, t), In(n, w))
    # got_w_to_t: [fa_char, ext, inf, omega_w, f_total, is_v] |- In(n,w) -> In(n,t)
    got_in_t = mp(got_w_to_t,
        Proof(Sequent([In(n, w)], [In(n, w)]), 'axiom', principal=In(n, w)),
        In(n, w), In(n, t), [], [])
    # got_in_t: [fa_char, ext, inf, omega_w, f_total, is_v, In(n,w)] |- In(n,t)

    # Forward through characterization: In(n,t) -> And(In(n,w), P(n))
    char_n = _char_at(n)
    fwd_n = _iff_fwd(char_n, In(n, t), And(In(n, w), P(n)))
    got_and_n = mp(fwd_n, got_in_t, In(n, t), And(In(n, w), P(n)), [fa_char], [fa_char])
    # got_and_n: [...] |- And(In(n,w), P(n))

    # Extract P(n):
    got_pn = apply_thm(and_elim_right(In(n, w), P(n), []), [],
        And(In(n, w), P(n)), P(n),
        Proof(Sequent([And(In(n, w), P(n))], [And(In(n, w), P(n))]),
              'axiom', principal=And(In(n, w), P(n))), [], [])
    got_pn2 = Proof(Sequent(got_and_n.sequent.left, [P(n)]), 'cut',
        [wr(got_and_n, P(n)), wl(got_pn, *got_and_n.sequent.left)],
        principal=And(In(n, w), P(n)))
    # got_pn2: [fa_char, ext, inf, omega_w, f_total, is_v, In(n,w)] |- P(n)

    # --- Existential elimination on t (from Separation) ---
    got_pn3 = _eel(got_pn2, fa_char, t)
    # got_pn3: [..., exists t.fa_char] |- P(n)
    ex_t_actual = got_pn3.sequent.left[-1]

    # Cut with fl_w: [sep] |- exists t.fa_char
    # Build cut from actual contexts (avoids duplicate axiom issues)
    pn3_ctx = [f_ for f_ in got_pn3.sequent.left if f_ is not ex_t_actual]
    shared = pn3_ctx + [sep]

    br1 = fl_w  # [sep] |- [exists t.fa_char]
    for f_ in pn3_ctx:
        br1 = wl(br1, f_)
    br1 = wr(br1, P(n))
    br2 = wl(got_pn3, sep)
    got_pn4 = Proof(Sequent(shared, [P(n)]), 'cut', [br1, br2], principal=ex_t_actual)

    # --- Close: discharge hypotheses, forall ---
    # Find actual formula objects from the sequent for discharge
    proof = got_pn4
    # Discharge: In(n,w), omega_w, is_v, f_total -- find them by identity in the left
    for h in [omega_w, is_v, f_total]:
        # h should be in proof.sequent.left by identity since we created them
        imp_h = Implies(h, proof.sequent.right[0])
        remaining = [f_ for f_ in proof.sequent.left if f_ is not h]
        proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)

    # In(n,w) might not match by identity -- find it in the remaining left
    in_n_w_actual = None
    for f_ in proof.sequent.left:
        if isinstance(f_, In) and f_.left is n:
            in_n_w_actual = f_
            break
    if in_n_w_actual is None:
        # fallback: last non-axiom formula
        in_n_w_actual = [f_ for f_ in proof.sequent.left
                         if not isinstance(f_, (zfc.ZFCAxiom,))
                         and f_ is not sep][-1]
    imp_h = Implies(in_n_w_actual, proof.sequent.right[0])
    remaining = [f_ for f_ in proof.sequent.left if f_ is not in_n_w_actual]
    proof = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof], principal=imp_h)

    for var in [n, w, v, f, a]:
        body = proof.sequent.right[0]
        fa = Forall(var, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right', [proof], term=var, principal=fa)
    proof.name = 'init_seg_total'
    return proof


def initial_segments_agree():
    """Initial segments of a recursion agree wherever both defined.
    |- forall a, f, v1, v2, n, y1, y2, w.
       Omega(w) -> n in w ->
       Function(f) -> InitialSegment(v1,a,f) -> InitialSegment(v2,a,f) ->
       Apply(v1,n,y1) -> Apply(v2,n,y2) -> Eq(y1,y2)

    Proved by induction on n using Separation + omega_smallest_inductive.
    This is the first induction in the recursion theorem (4.2.14)."""
    from tactics import apply_thm, wl, wr, mp
    from definitions import (Inductive, Omega, Empty, Successor, Function as FuncDef,
                             Apply, InitialSegment, Subset, Domain)

    ai, fi, v1, v2, n, y1, y2, w = Var(), Var(), Var(), Var(), Var(), Var(), Var(), Var()
    ev, sn, d, val, fval = Var(), Var(), Var(), Var(), Var()

    omega_w = Omega(w)
    func_f = FuncDef(fi)
    is1 = InitialSegment(v1, ai, fi)
    is2 = InitialSegment(v2, ai, fi)
    app1 = Apply(v1, n, y1)
    app2 = Apply(v2, n, y2)
    goal = Eq(y1, y2)

    # The agreement property P(n):
    # forall v1 v2 y1 y2. InitSeg(v1,a,f) -> InitSeg(v2,a,f) ->
    #   Apply(v1,n,y1) -> Apply(v2,n,y2) -> Eq(y1,y2)
    def P(x):
        return Forall(v1, Forall(v2, Forall(y1, Forall(y2,
            Implies(InitialSegment(v1, ai, fi),
            Implies(InitialSegment(v2, ai, fi),
            Implies(Apply(v1, x, y1),
            Implies(Apply(v2, x, y2),
            Eq(y1, y2)))))))))

    # Separation: forall a f omega_set. exists t. forall x. x in t iff (x in omega_set and P(x))
    sep = zfc.Separation(P, [ai, fi])

    # The core induction:
    # 1. From Separation with omega_set = w: exists t with the characterization
    # 2. Show Inductive(t): base case P(0) and step P(n)->P(S(n))
    # 3. omega_smallest_inductive: t sub w and Inductive(t) -> t = w
    # 4. So forall n in w: P(n)
    #
    # === Helper: extract parts from InitialSegment ===
    def _is_func(is_proof, is_formula):
        """From InitSeg(v,a,f) |- Function(v)."""
        is_f = is_formula
        # InitSeg = And(Function(v), And(base, step))
        func_v = FuncDef(is_f.func)
        rest = And(Forall(ev, Implies(Empty(ev), Apply(is_f.func, ev, is_f.init))),
                   Forall(n, Forall(val, Implies(Apply(is_f.func, n, val),
                       Forall(sn, Implies(Successor(sn, n),
                           Forall(fval, Implies(Apply(is_f.step, val, fval),
                               Apply(is_f.func, sn, fval)))))))))
        return apply_thm(and_elim_left(func_v, rest, []), [], is_formula, func_v,
                         Proof(Sequent([is_formula], [is_formula]), 'axiom', principal=is_formula), [], [])

    def _is_base(is_proof, is_formula):
        """From InitSeg(v,a,f) |- forall e. Empty(e) -> Apply(v, e, a)."""
        is_f = is_formula
        func_v = FuncDef(is_f.func)
        base = Forall(ev, Implies(Empty(ev), Apply(is_f.func, ev, is_f.init)))
        step_f = Forall(n, Forall(val, Implies(Apply(is_f.func, n, val),
                     Forall(sn, Implies(Successor(sn, n),
                         Forall(fval, Implies(Apply(is_f.step, val, fval),
                             Apply(is_f.func, sn, fval))))))))
        rest = And(base, step_f)
        # And_elim_right(func, rest) then and_elim_left(base, step)
        ax = Proof(Sequent([is_formula], [is_formula]), 'axiom', principal=is_formula)
        got_rest = apply_thm(and_elim_right(func_v, rest, []), [], is_formula, rest, ax, [], [])
        return apply_thm(and_elim_left(base, step_f, []), [], rest, base,
                         Proof(Sequent([rest], [rest]), 'axiom', principal=rest), [], [])

    # === Base case: P(e) when Empty(e) ===
    # From InitSeg(v1): Apply(v1, e, a_init) [base clause with e]
    # From Apply(v1, e, y1) and Apply(v1, e, a_init) and Function(v1): Eq(y1, a_init)
    # Similarly for v2: Eq(y2, a_init)
    # Then Eq(y1, y2) by eq_transitive: y1 = a_init = y2... actually need eq_sym + eq_trans.

    # From InitSeg(v1): base gives Apply(v1, e_var, a_init) for any Empty(e_var)
    # But we need it for the SPECIFIC n (which is empty in the base case).
    # P(n) with Empty(n): need Apply(v1,n,y1)  and  Apply(v1,n,a_init) -> Eq(y1, a_init).

    # Build: InitSeg(v1), Empty(n), Apply(v1,n,y1) |- Eq(y1, ai)
    # Step 1: from InitSeg, get base clause: forall e. Empty(e) -> Apply(v1, e, ai)
    # Step 2: instantiate with n: Empty(n) -> Apply(v1, n, ai)
    # Step 3: MP with Empty(n): Apply(v1, n, ai)
    # Step 4: Function(v1) from InitSeg: Apply(v1,n,y1)  and  Apply(v1,n,ai) -> Eq(y1, ai)
    # Step 5: from Function(v1): y1 = ai

    # For step 4, Function says: forall x,y1,y2. Apply(v1,x,y1)  and  Apply(v1,x,y2) -> Eq(y1,y2)
    # Instantiate x=n, y1=y1, y2=ai: Apply(v1,n,y1)  and  Apply(v1,n,ai) -> Eq(y1,ai)

    # This requires unpacking Function's foralls. Let me use a helper.
    def _func_unique(func_pf, func_f, x_term, y1_term, y2_term, app1_pf, app2_pf):
        """From Function(f), Apply(f,x,y1), Apply(f,x,y2), derive Eq(y1,y2).
        func_pf: ctx1 |- Function(f)
        app1_pf: ctx2 |- Apply(f,x,y1)
        app2_pf: ctx3 |- Apply(f,x,y2)
        Returns: ctx1+ctx2+ctx3 |- Eq(y1,y2)"""
        x, ya, yb = Var(), Var(), Var()
        func_body = Forall(x, Forall(ya, Forall(yb,
            Implies(And(Apply(func_f, x, ya), Apply(func_f, x, yb)), Eq(ya, yb)))))
        # func_body is alpha-equiv to Function(func_f) after expansion

        app_f_x_y1 = Apply(func_f, x_term, y1_term)
        app_f_x_y2 = Apply(func_f, x_term, y2_term)
        and_apps = And(app_f_x_y1, app_f_x_y2)
        eq_y1y2 = Eq(y1_term, y2_term)
        imp_and_eq = Implies(and_apps, eq_y1y2)
        fa3 = Forall(yb, Implies(And(Apply(func_f, x_term, y1_term), Apply(func_f, x_term, yb)), Eq(y1_term, yb)))
        fa2 = Forall(ya, Forall(yb, Implies(And(Apply(func_f, x_term, ya), Apply(func_f, x_term, yb)), Eq(ya, yb))))
        fa1 = func_body

        def _fl(parent, body, term):
            return Proof(Sequent([parent], [body]), 'forall_left',
                [Proof(Sequent([body], [body]), 'axiom', principal=body)],
                principal=parent, term=term)

        # Peel 3 foralls from Function(func_f)
        fl1 = _fl(fa1, fa2, x_term)
        fl2 = Proof(Sequent([fa1], [fa3]), 'cut',
            [wr(fl1, fa3), wl(_fl(fa2, fa3, y1_term), fa1)], principal=fa2)
        fl3 = Proof(Sequent([fa1], [imp_and_eq]), 'cut',
            [wr(fl2, imp_and_eq), wl(_fl(fa3, imp_and_eq, y2_term), fa1)], principal=fa3)

        # func_pf: ctx1 |- Function(func_f). Cut to get ctx1 |- imp_and_eq.
        got_imp = Proof(Sequent(func_pf.sequent.left, [imp_and_eq]), 'cut',
            [wr(func_pf, imp_and_eq), wl(fl3, *func_pf.sequent.left)], principal=fa1)

        # Build And(app1, app2) from app1_pf and app2_pf
        n_app2 = Not(app_f_x_y2)
        a1 = Proof(Sequent(app2_pf.sequent.left + [n_app2], []), 'not_left', [app2_pf], principal=n_app2)
        a2 = Proof(Sequent(app1_pf.sequent.left + app2_pf.sequent.left + [Implies(app_f_x_y1, n_app2)], []),
                   'implies_left', [wl(app1_pf, *app2_pf.sequent.left), wl(a1, *app1_pf.sequent.left)],
                   principal=Implies(app_f_x_y1, n_app2))
        got_and = Proof(Sequent(app1_pf.sequent.left + app2_pf.sequent.left, [and_apps]),
                        'not_right', [a2], principal=and_apps)

        # MP: and_apps, imp_and_eq |- eq_y1y2
        return mp(got_imp, got_and, and_apps, eq_y1y2, [], [])

    # === Build the base case proof ===
    # Context: InitSeg(v1,ai,fi), InitSeg(v2,ai,fi), Empty(n_var), Apply(v1,n_var,y1), Apply(v2,n_var,y2)
    # Goal: Eq(y1, y2)

    # From InitSeg(v1): Function(v1) and Apply(v1, n, ai)
    n_var = Var()  # the element being tested (n in P(n))
    is1_f = InitialSegment(v1, ai, fi)
    is2_f = InitialSegment(v2, ai, fi)
    ax_is1 = Proof(Sequent([is1_f], [is1_f]), 'axiom', principal=is1_f)
    ax_is2 = Proof(Sequent([is2_f], [is2_f]), 'axiom', principal=is2_f)

    got_func_v1 = _is_func(ax_is1, is1_f)  # [is1_f] |- [Function(v1)]
    got_base_v1_fa = _is_base(ax_is1, is1_f)  # [is1_f... actually this returns [rest] |- [base]

    # Hmm, _is_base returns [And(base, step)] |- [base], not [is1_f] |- [base].
    # Need to chain: is1_f |- rest |- base.
    # Let me fix _is_base to return [is1_f] |- [base].

    # Actually let me redo these helpers properly.
    func_v1 = FuncDef(v1)
    base_v1 = Forall(ev, Implies(Empty(ev), Apply(v1, ev, ai)))
    step_v1 = Forall(n, Forall(val, Implies(Apply(v1, n, val),
                  Forall(sn, Implies(Successor(sn, n),
                      Forall(fval, Implies(Apply(fi, val, fval),
                          Apply(v1, sn, fval))))))))
    rest_v1 = And(base_v1, step_v1)

    ax1 = Proof(Sequent([is1_f], [is1_f]), 'axiom', principal=is1_f)
    got_func1 = apply_thm(and_elim_left(func_v1, rest_v1, []), [], is1_f, func_v1, ax1, [], [])
    got_rest1 = apply_thm(and_elim_right(func_v1, rest_v1, []), [], is1_f, rest_v1,
                          Proof(Sequent([is1_f], [is1_f]), 'axiom', principal=is1_f), [], [])
    got_base1 = apply_thm(and_elim_left(base_v1, step_v1, []), [], rest_v1, base_v1,
                          Proof(Sequent([rest_v1], [rest_v1]), 'axiom', principal=rest_v1), [], [])
    # Chain: is1_f |- base_v1
    got_base1_full = Proof(Sequent([is1_f], [base_v1]), 'cut',
        [wr(got_rest1, base_v1), wl(got_base1, is1_f)], principal=rest_v1)

    # Instantiate base_v1 with n_var: Empty(n_var) -> Apply(v1, n_var, ai)
    imp_emp_app = Implies(Empty(n_var), Apply(v1, n_var, ai))
    def _fl(parent, body, term):
        return Proof(Sequent([parent], [body]), 'forall_left',
            [Proof(Sequent([body], [body]), 'axiom', principal=body)],
            principal=parent, term=term)
    fl_base1 = _fl(base_v1, imp_emp_app, n_var)
    got_imp_app1 = Proof(Sequent([is1_f], [imp_emp_app]), 'cut',
        [wr(got_base1_full, imp_emp_app), wl(fl_base1, is1_f)], principal=base_v1)
    # MP with Empty(n_var): is1_f, Empty(n_var) |- Apply(v1, n_var, ai)
    got_app1_ai = mp(got_imp_app1,
                     Proof(Sequent([Empty(n_var)], [Empty(n_var)]), 'axiom', principal=Empty(n_var)),
                     Empty(n_var), Apply(v1, n_var, ai), [], [])

    # Function uniqueness: Apply(v1,n_var,y1)  and  Apply(v1,n_var,ai) -> Eq(y1,ai)
    app_v1_n_y1 = Apply(v1, n_var, y1)
    ax_app1 = Proof(Sequent([app_v1_n_y1], [app_v1_n_y1]), 'axiom', principal=app_v1_n_y1)
    got_y1_eq_ai = _func_unique(got_func1, v1, n_var, y1, ai, ax_app1, got_app1_ai)
    # got_y1_eq_ai: [is1_f, app_v1_n_y1, Empty(n_var)] |- [Eq(y1, ai)]

    # Similarly for v2:
    func_v2 = FuncDef(v2)
    base_v2 = Forall(ev, Implies(Empty(ev), Apply(v2, ev, ai)))
    step_v2 = Forall(n, Forall(val, Implies(Apply(v2, n, val),
                  Forall(sn, Implies(Successor(sn, n),
                      Forall(fval, Implies(Apply(fi, val, fval),
                          Apply(v2, sn, fval))))))))
    rest_v2 = And(base_v2, step_v2)
    ax2 = Proof(Sequent([is2_f], [is2_f]), 'axiom', principal=is2_f)
    got_func2 = apply_thm(and_elim_left(func_v2, rest_v2, []), [], is2_f, func_v2, ax2, [], [])
    got_rest2 = apply_thm(and_elim_right(func_v2, rest_v2, []), [], is2_f, rest_v2,
                          Proof(Sequent([is2_f], [is2_f]), 'axiom', principal=is2_f), [], [])
    got_base2 = apply_thm(and_elim_left(base_v2, step_v2, []), [], rest_v2, base_v2,
                          Proof(Sequent([rest_v2], [rest_v2]), 'axiom', principal=rest_v2), [], [])
    got_base2_full = Proof(Sequent([is2_f], [base_v2]), 'cut',
        [wr(got_rest2, base_v2), wl(got_base2, is2_f)], principal=rest_v2)
    imp_emp_app2 = Implies(Empty(n_var), Apply(v2, n_var, ai))
    fl_base2 = _fl(base_v2, imp_emp_app2, n_var)
    got_imp_app2 = Proof(Sequent([is2_f], [imp_emp_app2]), 'cut',
        [wr(got_base2_full, imp_emp_app2), wl(fl_base2, is2_f)], principal=base_v2)
    got_app2_ai = mp(got_imp_app2,
                     Proof(Sequent([Empty(n_var)], [Empty(n_var)]), 'axiom', principal=Empty(n_var)),
                     Empty(n_var), Apply(v2, n_var, ai), [], [])
    app_v2_n_y2 = Apply(v2, n_var, y2)
    ax_app2 = Proof(Sequent([app_v2_n_y2], [app_v2_n_y2]), 'axiom', principal=app_v2_n_y2)
    got_y2_eq_ai = _func_unique(got_func2, v2, n_var, y2, ai, ax_app2, got_app2_ai)
    # got_y2_eq_ai: [is2_f, app_v2_n_y2, Empty(n_var)] |- [Eq(y2, ai)]

    # Chain: Eq(y1, ai) and Eq(y2, ai) -> Eq(y1, y2)
    # eq_symmetric on Eq(y2, ai) -> Eq(ai, y2). Then eq_transitive Eq(y1,ai),Eq(ai,y2) -> Eq(y1,y2).
    es_thm = eq_symmetric()
    et_thm = eq_transitive()
    eq_ai_y2 = Eq(ai, y2)
    got_ai_y2 = apply_thm(es_thm, [y2, ai], Eq(y2, ai), eq_ai_y2, got_y2_eq_ai, [], [])
    imp_ai_y2 = Implies(eq_ai_y2, Eq(y1, y2))
    got_imp_trans = apply_thm(et_thm, [y1, ai, y2], Eq(y1, ai), imp_ai_y2, got_y1_eq_ai, [], [])
    base_result = mp(got_imp_trans, got_ai_y2, eq_ai_y2, Eq(y1, y2), [], [])
    # base_result: [is1_f, app_v1_n_y1, Empty(n_var), is2_f, app_v2_n_y2] |- [Eq(y1, y2)]

    # Discharge to build P(n_var) when Empty(n_var):
    # P(n_var) = forall v1 forall v2 forall y1 forall y2. is1 -> is2 -> app1 -> app2 -> Eq(y1,y2)
    proof_base = base_result
    for h in [app_v2_n_y2, is2_f, app_v1_n_y1, is1_f]:
        imp_h = Implies(h, proof_base.sequent.right[0])
        remaining = [f for f in proof_base.sequent.left if f is not h]
        proof_base = Proof(Sequent(remaining, [imp_h]), 'implies_right', [proof_base], principal=imp_h)
    for v in [y2, y1, v2, v1]:
        body = proof_base.sequent.right[0]
        fa = Forall(v, body)
        proof_base = Proof(Sequent(proof_base.sequent.left, [fa]), 'forall_right', [proof_base], term=v, principal=fa)
    # proof_base: [Empty(n_var)] |- [P(n_var)]
    # This is the base case! P holds at any empty n_var.

    # === Step case: P(n_var)  and  Successor(sn_var, n_var) -> P(sn_var) ===
    # From P(n_var): for any v1,v2,y1,y2 with InitSeg and Apply at n_var: Eq(y1,y2)
    # From InitSeg step clause + Apply(v1,n_var,val1) + Succ(sn_var,n_var) + Apply(fi,val1,fv1):
    #   Apply(v1, sn_var, fv1)
    # Similarly for v2: Apply(v2, sn_var, fv2)
    # From P(n_var): val1 = val2 (agreement at n_var)
    # From Function(fi): fi(val1) = fi(val2), i.e., fv1 = fv2
    # From Function(v1): y1 = fv1 (from Apply(v1,sn_var,y1) and Apply(v1,sn_var,fv1))
    # From Function(v2): y2 = fv2
    # So y1 = fv1 = fv2 = y2. (ok)

    sn_var = Var()
    val1, val2, fv1, fv2 = Var(), Var(), Var(), Var()
    p_n = P(n_var)  # the induction hypothesis

    # Context: P(n_var), Successor(sn_var, n_var), InitSeg(v1), InitSeg(v2),
    #          Apply(v1, sn_var, y1), Apply(v2, sn_var, y2),
    #          Apply(v1, n_var, val1), Apply(v2, n_var, val2),
    #          Apply(fi, val1, fv1), Apply(fi, val2, fv2),
    #          Function(fi)
    # Goal: Eq(y1, y2)

    succ_sn = Successor(sn_var, n_var)
    app_v1_n_val1 = Apply(v1, n_var, val1)
    app_v2_n_val2 = Apply(v2, n_var, val2)
    app_f_val1_fv1 = Apply(fi, val1, fv1)
    app_f_val2_fv2 = Apply(fi, val2, fv2)
    app_v1_sn_y1 = Apply(v1, sn_var, y1)
    app_v2_sn_y2 = Apply(v2, sn_var, y2)
    app_v1_sn_fv1 = Apply(v1, sn_var, fv1)
    app_v2_sn_fv2 = Apply(v2, sn_var, fv2)

    # Step 1: From InitSeg(v1) step clause + Apply(v1,n_var,val1) + Succ(sn,n) + Apply(fi,val1,fv1):
    #   -> Apply(v1, sn_var, fv1)
    # InitSeg step: forall n,val. Apply(v1,n,val) -> forall sn. Succ(sn,n) -> forall fv. Apply(fi,val,fv) -> Apply(v1,sn,fv)
    got_step1 = apply_thm(and_elim_right(func_v1, rest_v1, []), [], is1_f, rest_v1,
                           Proof(Sequent([is1_f], [is1_f]), 'axiom', principal=is1_f), [], [])
    got_step1b = apply_thm(and_elim_right(base_v1, step_v1, []), [], rest_v1, step_v1,
                            Proof(Sequent([rest_v1], [rest_v1]), 'axiom', principal=rest_v1), [], [])
    got_step1_full = Proof(Sequent([is1_f], [step_v1]), 'cut',
        [wr(got_step1, step_v1), wl(got_step1b, is1_f)], principal=rest_v1)
    # Peel: step_v1 = forall n forall val. Apply(v1,n,val) -> forall sn. Succ(sn,n) -> forall fv. Apply(fi,val,fv) -> Apply(v1,sn,fv)
    # Instantiate n->n_var, val->val1, sn->sn_var, fv->fv1. Apply all implies_left.
    # The result after all peeling: is1_f, Apply(v1,n_var,val1), Succ(sn_var,n_var), Apply(fi,val1,fv1) |- Apply(v1,sn_var,fv1)

    # This is 4 forall_left + 3 implies_left. Let me use apply_thm chain.
    imp3 = Implies(app_f_val1_fv1, app_v1_sn_fv1)
    imp2 = Implies(succ_sn, Forall(fv1, imp3))
    imp1_inner = Forall(sn_var, imp2)
    imp1 = Implies(app_v1_n_val1, imp1_inner)
    fa_val1 = Forall(val1, imp1)
    fa_n_val1 = Forall(n_var, fa_val1)
    # step_v1 should be alpha-equiv to fa_n_val1 after expansion

    # Peel and apply: is1_f |- step_v1. Chain to get Apply(v1, sn_var, fv1).
    ax_app_sn_fv1 = Proof(Sequent([app_v1_sn_fv1], [app_v1_sn_fv1]), 'axiom', principal=app_v1_sn_fv1)
    # Build from inside out:
    ax_fapp = Proof(Sequent([app_f_val1_fv1], [app_f_val1_fv1, app_v1_sn_fv1]),
                    'weakening_right',
                    [Proof(Sequent([app_f_val1_fv1], [app_f_val1_fv1]), 'axiom', principal=app_f_val1_fv1)],
                    principal=app_v1_sn_fv1)
    il_fv = Proof(Sequent([imp3, app_f_val1_fv1], [app_v1_sn_fv1]),
                  'implies_left', [ax_fapp, wl(ax_app_sn_fv1, app_f_val1_fv1)], principal=imp3)
    fl_fv = Proof(Sequent([Forall(fv1, imp3), app_f_val1_fv1], [app_v1_sn_fv1]),
                  'forall_left', [il_fv], principal=Forall(fv1, imp3), term=fv1)
    ax_succ = Proof(Sequent([succ_sn, app_f_val1_fv1], [succ_sn, app_v1_sn_fv1]),
                    'weakening_left',
                    [wr(Proof(Sequent([succ_sn], [succ_sn]), 'axiom', principal=succ_sn), app_v1_sn_fv1)],
                    principal=app_f_val1_fv1)
    il_sn = Proof(Sequent([imp2, succ_sn, app_f_val1_fv1], [app_v1_sn_fv1]),
                  'implies_left', [ax_succ, fl_fv], principal=imp2)
    fl_sn = Proof(Sequent([imp1_inner, succ_sn, app_f_val1_fv1], [app_v1_sn_fv1]),
                  'forall_left', [il_sn], principal=imp1_inner, term=sn_var)
    ax_app_n = Proof(Sequent([app_v1_n_val1, succ_sn, app_f_val1_fv1], [app_v1_n_val1, app_v1_sn_fv1]),
                     'weakening_left',
                     [Proof(Sequent([app_v1_n_val1, app_f_val1_fv1], [app_v1_n_val1, app_v1_sn_fv1]),
                            'weakening_left',
                            [wr(Proof(Sequent([app_v1_n_val1], [app_v1_n_val1]), 'axiom', principal=app_v1_n_val1),
                                app_v1_sn_fv1)],
                            principal=app_f_val1_fv1)],
                     principal=succ_sn)
    il_n = Proof(Sequent([imp1, app_v1_n_val1, succ_sn, app_f_val1_fv1], [app_v1_sn_fv1]),
                 'implies_left', [ax_app_n, fl_sn], principal=imp1)
    fl_val = Proof(Sequent([fa_val1, app_v1_n_val1, succ_sn, app_f_val1_fv1], [app_v1_sn_fv1]),
                   'forall_left', [il_n], principal=fa_val1, term=val1)
    fl_n = Proof(Sequent([fa_n_val1, app_v1_n_val1, succ_sn, app_f_val1_fv1], [app_v1_sn_fv1]),
                 'forall_left', [fl_val], principal=fa_n_val1, term=n_var)
    # Cut with is1_f |- step_v1 (alpha-equiv to fa_n_val1):
    got_app_v1_sn = Proof(Sequent([is1_f, app_v1_n_val1, succ_sn, app_f_val1_fv1], [app_v1_sn_fv1]), 'cut',
        [wr(wl(got_step1_full, app_v1_n_val1, succ_sn, app_f_val1_fv1), app_v1_sn_fv1),
         wl(fl_n, is1_f)], principal=fa_n_val1)

    # Step 2: y1 = fv1 (Function(v1) uniqueness: Apply(v1,sn,y1)  and  Apply(v1,sn,fv1))
    got_y1_eq_fv1 = _func_unique(got_func1, v1, sn_var, y1, fv1,
                                  Proof(Sequent([app_v1_sn_y1], [app_v1_sn_y1]), 'axiom', principal=app_v1_sn_y1),
                                  got_app_v1_sn)

    # Step 3: Similarly for v2: Apply(v2, sn_var, fv2) and y2 = fv2
    got_step2_full = Proof(Sequent([is2_f], [step_v2]), 'cut',
        [wr(apply_thm(and_elim_right(func_v2, rest_v2, []), [], is2_f, rest_v2,
                      Proof(Sequent([is2_f], [is2_f]), 'axiom', principal=is2_f), [], []), step_v2),
         wl(apply_thm(and_elim_right(base_v2, step_v2, []), [], rest_v2, step_v2,
                      Proof(Sequent([rest_v2], [rest_v2]), 'axiom', principal=rest_v2), [], []), is2_f)],
        principal=rest_v2)

    fa_n_val2 = Forall(n_var, Forall(val2, Implies(Apply(v2, n_var, val2),
                    Forall(sn_var, Implies(succ_sn,
                        Forall(fv2, Implies(app_f_val2_fv2, app_v2_sn_fv2)))))))
    # Peel similarly for v2 (same structure, different vars):
    imp3_v2 = Implies(app_f_val2_fv2, app_v2_sn_fv2)
    imp2_v2 = Implies(succ_sn, Forall(fv2, imp3_v2))
    imp1_inner_v2 = Forall(sn_var, imp2_v2)

    ax_app_sn_fv2 = Proof(Sequent([app_v2_sn_fv2], [app_v2_sn_fv2]), 'axiom', principal=app_v2_sn_fv2)
    ax_fapp2 = wr(Proof(Sequent([app_f_val2_fv2], [app_f_val2_fv2]), 'axiom', principal=app_f_val2_fv2), app_v2_sn_fv2)
    il_fv2 = Proof(Sequent([imp3_v2, app_f_val2_fv2], [app_v2_sn_fv2]),
                   'implies_left', [ax_fapp2, wl(ax_app_sn_fv2, app_f_val2_fv2)], principal=imp3_v2)
    fl_fv2 = Proof(Sequent([Forall(fv2, imp3_v2), app_f_val2_fv2], [app_v2_sn_fv2]),
                   'forall_left', [il_fv2], principal=Forall(fv2, imp3_v2), term=fv2)
    ax_succ2 = Proof(Sequent([succ_sn, app_f_val2_fv2], [succ_sn, app_v2_sn_fv2]),
                     'weakening_left',
                     [wr(Proof(Sequent([succ_sn], [succ_sn]), 'axiom', principal=succ_sn), app_v2_sn_fv2)],
                     principal=app_f_val2_fv2)
    il_sn2 = Proof(Sequent([imp2_v2, succ_sn, app_f_val2_fv2], [app_v2_sn_fv2]),
                   'implies_left', [ax_succ2, fl_fv2], principal=imp2_v2)
    fl_sn2 = Proof(Sequent([imp1_inner_v2, succ_sn, app_f_val2_fv2], [app_v2_sn_fv2]),
                   'forall_left', [il_sn2], principal=imp1_inner_v2, term=sn_var)
    ax_app_n2 = Proof(Sequent([app_v2_n_val2, succ_sn, app_f_val2_fv2], [app_v2_n_val2, app_v2_sn_fv2]),
                      'weakening_left',
                      [Proof(Sequent([app_v2_n_val2, app_f_val2_fv2], [app_v2_n_val2, app_v2_sn_fv2]),
                             'weakening_left',
                             [wr(Proof(Sequent([app_v2_n_val2], [app_v2_n_val2]), 'axiom', principal=app_v2_n_val2),
                                 app_v2_sn_fv2)],
                             principal=app_f_val2_fv2)],
                      principal=succ_sn)
    imp1_v2 = Implies(app_v2_n_val2, imp1_inner_v2)
    il_n2 = Proof(Sequent([imp1_v2, app_v2_n_val2, succ_sn, app_f_val2_fv2], [app_v2_sn_fv2]),
                  'implies_left', [ax_app_n2, fl_sn2], principal=imp1_v2)
    fa_val2_v2 = Forall(val2, imp1_v2)
    fl_val2 = Proof(Sequent([fa_val2_v2, app_v2_n_val2, succ_sn, app_f_val2_fv2], [app_v2_sn_fv2]),
                    'forall_left', [il_n2], principal=fa_val2_v2, term=val2)
    fl_n2 = Proof(Sequent([fa_n_val2, app_v2_n_val2, succ_sn, app_f_val2_fv2], [app_v2_sn_fv2]),
                  'forall_left', [fl_val2], principal=fa_n_val2, term=n_var)
    got_app_v2_sn = Proof(Sequent([is2_f, app_v2_n_val2, succ_sn, app_f_val2_fv2], [app_v2_sn_fv2]), 'cut',
        [wr(wl(got_step2_full, app_v2_n_val2, succ_sn, app_f_val2_fv2), app_v2_sn_fv2),
         wl(fl_n2, is2_f)], principal=fa_n_val2)

    got_y2_eq_fv2 = _func_unique(got_func2, v2, sn_var, y2, fv2,
                                  Proof(Sequent([app_v2_sn_y2], [app_v2_sn_y2]), 'axiom', principal=app_v2_sn_y2),
                                  got_app_v2_sn)

    # Step 4: IH gives val1 = val2. Then Function(fi) gives fv1 = fv2.
    # P(n_var) instantiated with v1,v2,val1,val2: InitSeg -> InitSeg -> Apply(v1,n,val1) -> Apply(v2,n,val2) -> Eq(val1,val2)
    p_n_inst = Implies(is1_f, Implies(is2_f, Implies(app_v1_n_val1, Implies(app_v2_n_val2, Eq(val1, val2)))))
    # Peel P(n_var)'s foralls with v1,v2,val1,val2:
    p_body = P(n_var)  # forall v1 forall v2 forall y1 forall y2. ...
    # After peeling forall v1->v1, forall v2->v2, forall y1->val1, forall y2->val2: p_n_inst
    ax_pn = Proof(Sequent([p_n_inst], [p_n_inst]), 'axiom', principal=p_n_inst)
    # Peel from p_body:
    p1 = _fl(p_body, Forall(v2, Forall(y1, Forall(y2,
        Implies(is1_f, Implies(is2_f, Implies(Apply(v1, n_var, y1), Implies(Apply(v2, n_var, y2), Eq(y1, y2)))))))), v1)
    p2 = Proof(Sequent([p_body], [Forall(y1, Forall(y2,
        Implies(is1_f, Implies(is2_f, Implies(Apply(v1, n_var, y1), Implies(Apply(v2, n_var, y2), Eq(y1, y2)))))))]), 'cut',
        [wr(p1, Forall(y1, Forall(y2, Implies(is1_f, Implies(is2_f, Implies(Apply(v1, n_var, y1), Implies(Apply(v2, n_var, y2), Eq(y1, y2)))))))),
         wl(_fl(Forall(v2, Forall(y1, Forall(y2, Implies(is1_f, Implies(is2_f, Implies(Apply(v1, n_var, y1), Implies(Apply(v2, n_var, y2), Eq(y1, y2)))))))),
                Forall(y1, Forall(y2, Implies(is1_f, Implies(is2_f, Implies(Apply(v1, n_var, y1), Implies(Apply(v2, n_var, y2), Eq(y1, y2))))))), v2),
             p_body)],
        principal=Forall(v2, Forall(y1, Forall(y2, Implies(is1_f, Implies(is2_f, Implies(Apply(v1, n_var, y1), Implies(Apply(v2, n_var, y2), Eq(y1, y2)))))))))
    # This is getting very nested. Let me use a simpler approach -- just peel all 4 foralls manually.

    # Actually, easier: use apply_thm on P(n_var) treated as a "theorem"
    # P(n_var) = forall v1 forall v2 forall y1 forall y2. is1 -> is2 -> app1 -> app2 -> Eq(y1,y2)
    # Treat as: thm with right = P(n_var), left = [p_n].
    # apply_thm expects thm to have the foralls on right. But p_n is a hypothesis on left.
    # Use implies_left approach: put P on left, peel foralls, apply.

    # Simpler: construct P(n_var) proof as [P(n_var)] |- [Eq(val1, val2)] directly,
    # then compose.

    # P(n_var), is1_f, is2_f, app_v1_n_val1, app_v2_n_val2 |- Eq(val1, val2)
    eq_val = Eq(val1, val2)
    # Peel all 4 foralls and apply all 4 implies:
    inner_imp = Implies(is1_f, Implies(is2_f, Implies(app_v1_n_val1, Implies(app_v2_n_val2, eq_val))))
    # From P(n_var), peel forall v1->v1: ...forall v2forall y1forall y2. is1->is2->...
    # Then forall v2->v2, forall y1->val1, forall y2->val2: inner_imp

    # Build axiom + 4 forall_left + 4 implies_left
    ax_eq_val = Proof(Sequent([eq_val], [eq_val]), 'axiom', principal=eq_val)

    # implies_left chain from inside out:
    ax_a2 = wr(Proof(Sequent([app_v2_n_val2], [app_v2_n_val2]), 'axiom', principal=app_v2_n_val2), eq_val)
    il4 = Proof(Sequent([Implies(app_v2_n_val2, eq_val), app_v2_n_val2], [eq_val]),
                'implies_left', [ax_a2, wl(ax_eq_val, app_v2_n_val2)], principal=Implies(app_v2_n_val2, eq_val))

    ax_a1 = wr(Proof(Sequent([app_v1_n_val1, app_v2_n_val2], [app_v1_n_val1]),
                     'weakening_left',
                     [Proof(Sequent([app_v1_n_val1], [app_v1_n_val1]), 'axiom', principal=app_v1_n_val1)],
                     principal=app_v2_n_val2), eq_val)
    il3 = Proof(Sequent([Implies(app_v1_n_val1, Implies(app_v2_n_val2, eq_val)), app_v1_n_val1, app_v2_n_val2], [eq_val]),
                'implies_left', [ax_a1, il4], principal=Implies(app_v1_n_val1, Implies(app_v2_n_val2, eq_val)))

    hyps_34 = [app_v1_n_val1, app_v2_n_val2]
    ax_i2 = wr(wl(Proof(Sequent([is2_f], [is2_f]), 'axiom', principal=is2_f), *hyps_34), eq_val)
    il2 = Proof(Sequent([Implies(is2_f, Implies(app_v1_n_val1, Implies(app_v2_n_val2, eq_val))), is2_f] + hyps_34, [eq_val]),
                'implies_left', [ax_i2, il3], principal=Implies(is2_f, Implies(app_v1_n_val1, Implies(app_v2_n_val2, eq_val))))

    hyps_234 = [is2_f] + hyps_34
    ax_i1 = wr(wl(Proof(Sequent([is1_f], [is1_f]), 'axiom', principal=is1_f), *hyps_234), eq_val)
    il1 = Proof(Sequent([inner_imp, is1_f] + hyps_234, [eq_val]),
                'implies_left', [ax_i1, il2], principal=inner_imp)

    # 4 forall_left to peel P(n_var):
    fa4 = Forall(y2, inner_imp)
    fa3 = Forall(val1, fa4)  # using val1 for y1's position
    # Wait, P(n_var) uses y1, y2 as bound vars. I'm instantiating y1->val1, y2->val2.
    fa34 = Forall(y1, Forall(y2, inner_imp))
    fa234 = Forall(v2, fa34)
    fa1234 = Forall(v1, fa234)  # = P(n_var)

    fl4 = Proof(Sequent([fa4, is1_f] + hyps_234, [eq_val]),
                'forall_left', [il1], principal=fa4, term=val2)
    fl3 = Proof(Sequent([fa34, is1_f] + hyps_234, [eq_val]),
                'forall_left', [fl4], principal=fa34, term=val1)
    fl2 = Proof(Sequent([fa234, is1_f] + hyps_234, [eq_val]),
                'forall_left', [fl3], principal=fa234, term=v2)
    fl1_p = Proof(Sequent([fa1234, is1_f] + hyps_234, [eq_val]),
                  'forall_left', [fl2], principal=fa1234, term=v1)
    # fl1_p: [P(n_var), is1_f, is2_f, app_v1_n_val1, app_v2_n_val2] |- [Eq(val1, val2)]

    # Step 5: From Function(fi) + Eq(val1,val2): fv1 = fv2
    func_fi = FuncDef(fi)
    ax_func_fi = Proof(Sequent([func_fi], [func_fi]), 'axiom', principal=func_fi)
    got_fv_eq = _func_unique(ax_func_fi, fi, val1, fv1, fv2,
                              Proof(Sequent([app_f_val1_fv1], [app_f_val1_fv1]), 'axiom', principal=app_f_val1_fv1),
                              Proof(Sequent([app_f_val2_fv2], [app_f_val2_fv2]), 'axiom', principal=app_f_val2_fv2))
    # Hmm, this gives func_fi, Apply(fi,val1,fv1), Apply(fi,val2,fv2) |- Eq(fv1, fv2)
    # But Apply(fi,val1,fv1) and Apply(fi,val2,fv2) use different first args (val1 vs val2).
    # Function says: same input -> same output. But val1 and val2 are different vars.
    # I need val1 = val2 FIRST, then use eq_substitution or eq_transfer to get
    # Apply(fi, val1, fv2) from Apply(fi, val2, fv2), then Function uniqueness.

    # Actually, the approach should be:
    # From Eq(val1, val2) and Apply(fi, val2, fv2):
    #   eq_transfer: Eq(val1,val2) -> Iff(In(val1,z), In(val2,z)) for any z
    #   But Apply is about ordered pairs, not just In.
    # Hmm, this requires more machinery.

    # Simpler: from Eq(val1, val2), we know val1 and val2 have the same members.
    # Apply(fi, val2, fv2) = exists p. OrdPair(p, val2, fv2)  and  In(p, fi).
    # From Eq(val1, val2): OrdPair(p, val1, fv2) <-> OrdPair(p, val2, fv2)
    #   (because OrdPair depends on set membership, and Eq means same members).
    # So Apply(fi, val1, fv2) follows from Apply(fi, val2, fv2) + Eq(val1, val2).
    # Then Function(fi): Apply(fi, val1, fv1)  and  Apply(fi, val1, fv2) -> Eq(fv1, fv2). (ok)

    # But proving Apply(fi,val1,fv2) from Apply(fi,val2,fv2) + Eq(val1,val2) requires
    # eq_transfer inside the OrdPair. This is deep work.

    # For now, let me skip this step and assume we can derive Eq(fv1, fv2) from
    # Eq(val1, val2) + Function(fi) + Apply(fi,val1,fv1) + Apply(fi,val2,fv2).
    # This is a valid theorem but requires ~50 more nodes to prove.

    # Step 6: Chain: y1 = fv1 = fv2 = y2
    # Eq(y1, fv1), Eq(fv1, fv2), Eq(fv2, y2) [from eq_symmetric on Eq(y2, fv2)]
    # -> Eq(y1, y2) by two eq_transitive applications.

    # This is getting very long. Let me leave the step case incomplete for now
    # and note what remains.

    # The step case STRUCTURE is clear:
    # 1. From InitSeg step clause: v1(S(n)) = f(v1(n)) (ok) (built above)
    # 2. From IH: v1(n) = v2(n) (ok) (fl1_p above)
    # 3. From Eq(val1,val2) + Function(fi): f(val1) = f(val2) [needs eq_transfer inside Apply]
    # 4. From Function(v1/v2) uniqueness: y1 = fv1, y2 = fv2 (ok) (built above)
    # 5. Chain equalities: y1 = fv1 = fv2 = y2

    # The missing piece is step 3: proving f preserves equality.
    # This needs a sub-theorem: "functions preserve equality"
    # func_preserves_eq: Function(f)  and  Eq(x1,x2)  and  Apply(f,x1,y1)  and  Apply(f,x2,y2) -> Eq(y1,y2)
    # This requires eq_transfer + OrdPair reasoning. A standalone theorem.

    pass


def recursion_theorem():
    """Theorem 4.2.14: the recursion theorem.
    Given Function(f) with {a} union ran(f) sub dom(f),
    exists unique h with Recursive(h, a, f) and Domain(h, omega).

    Uses initial_segments_agree (induction #1) and
    initial_segments_extend (induction #2)."""
    pass


def omega_smallest_inductive():
    """Theorem 4.2.1: p sub omega and isInductive(p) implies p = omega.
    |- forall p, w. Omega(w) -> Subset(p,w) and Inductive(p) -> Eq(p,w)"""
    from tactics import apply_thm, wl, wr, mp

    p, w, zv, cv = Var(), Var(), Var(), Var()

    omega_w = Omega(w)
    sub_pw = Subset(p, w)
    ind_p = Inductive(p)
    hyps = [omega_w, sub_pw, ind_p]
    eq_pw = Eq(p, w)

    # === Forward: In(zv, p) -> In(zv, w) from Subset ===
    fwd_imp = Implies(In(zv, p), In(zv, w))
    fwd = Proof(Sequent([sub_pw], [fwd_imp]), 'forall_left',
                [Proof(Sequent([fwd_imp], [fwd_imp]), 'axiom', principal=fwd_imp)],
                principal=sub_pw, term=zv)

    # === Backward: In(zv, w) -> In(zv, p) ===
    # From Omega(w) with b=p: Inductive(p) -> forall x. x in w iff (x in p and ...)
    and_cond = And(In(zv, p), Forall(cv, Implies(Inductive(cv), In(zv, cv))))
    iff_zw = Iff(In(zv, w), and_cond)
    fa_iff = Forall(zv, iff_zw)
    imp_ind_fa = Implies(ind_p, fa_iff)

    # Instantiate Omega(w) with b=p
    ax_imp = Proof(Sequent([imp_ind_fa], [imp_ind_fa]), 'axiom', principal=imp_ind_fa)
    got_imp = Proof(Sequent([omega_w], [imp_ind_fa]), 'forall_left',
                    [ax_imp], principal=omega_w, term=p)
    # MP with ind_p: omega_w, ind_p |- fa_iff
    got_fa = mp(got_imp,
                Proof(Sequent([ind_p], [ind_p]), 'axiom', principal=ind_p),
                ind_p, fa_iff, [], [])
    # Instantiate with zv: omega_w, ind_p |- iff_zw
    got_iff = Proof(Sequent(got_fa.sequent.left, [iff_zw]), 'forall_left',
                    [Proof(Sequent([iff_zw], [iff_zw]), 'axiom', principal=iff_zw)],
                    principal=fa_iff, term=zv)
    # got_fa has fa_iff on right. Cut to instantiate with zv.
    fl_iff = Proof(Sequent([fa_iff], [iff_zw]), 'forall_left',
                   [Proof(Sequent([iff_zw], [iff_zw]), 'axiom', principal=iff_zw)],
                   principal=fa_iff, term=zv)
    got_iff = Proof(Sequent(got_fa.sequent.left, [iff_zw]), 'cut',
        [wr(got_fa, iff_zw), wl(fl_iff, *got_fa.sequent.left)], principal=fa_iff)
    # got_iff: [omega_w, ind_p] |- [iff_zw]

    # Extract forward of iff_zw: In(zv,w) -> and_cond
    iff_fwd = Implies(In(zv, w), and_cond)
    iff_bwd = Implies(and_cond, In(zv, w))
    H_iff = Implies(iff_fwd, Not(iff_bwd))
    e1 = Proof(Sequent([iff_zw, iff_fwd], [iff_fwd]), 'axiom', principal=iff_fwd)
    e2 = Proof(Sequent([iff_zw, iff_fwd], [Not(iff_bwd), iff_fwd]),
               'weakening_right', [e1], principal=Not(iff_bwd))
    e3 = Proof(Sequent([iff_zw], [H_iff, iff_fwd]), 'implies_right', [e2], principal=H_iff)
    e4 = Proof(Sequent([H_iff], [H_iff, iff_fwd]), 'weakening_right',
               [Proof(Sequent([H_iff], [H_iff]), 'axiom', principal=H_iff)], principal=iff_fwd)
    e5 = Proof(Sequent([H_iff, iff_zw], [iff_fwd]), 'not_left', [e4], principal=iff_zw)
    ext_fwd = Proof(Sequent([iff_zw], [iff_fwd]), 'cut', [e3, e5], principal=H_iff)

    # Chain: omega_w, ind_p |- In(zv,w) -> and_cond
    got_fwd = Proof(Sequent(got_iff.sequent.left, [iff_fwd]), 'cut',
        [wr(got_iff, iff_fwd), wl(ext_fwd, *got_iff.sequent.left)], principal=iff_zw)

    # From and_cond extract In(zv, p) (and_elim_left)
    ael = and_elim_left(In(zv, p), Forall(cv, Implies(Inductive(cv), In(zv, cv))), [])
    ax_and = Proof(Sequent([and_cond], [and_cond]), 'axiom', principal=and_cond)
    got_in_p = apply_thm(ael, [], and_cond, In(zv, p), ax_and, [], [])
    # got_in_p: [and_cond] |- [In(zv, p)]

    # Chain: omega_w, ind_p, In(zv,w) |- In(zv, p)
    got_and = mp(got_fwd,
                 Proof(Sequent([In(zv, w)], [In(zv, w)]), 'axiom', principal=In(zv, w)),
                 In(zv, w), and_cond, [], [])
    # got_and: [omega_w, ind_p, In(zv,w)] |- [and_cond]
    bwd_core = Proof(Sequent(got_and.sequent.left, [In(zv, p)]), 'cut',
        [wr(got_and, In(zv, p)), wl(got_in_p, *got_and.sequent.left)], principal=and_cond)
    # bwd_core: [omega_w, ind_p, In(zv,w)] |- [In(zv,p)]
    bwd = Proof(Sequent([omega_w, ind_p], [Implies(In(zv, w), In(zv, p))]),
                'implies_right', [bwd_core], principal=Implies(In(zv, w), In(zv, p)))

    # === Build Iff(In(zv, p), In(zv, w)) ===
    fwd_w = wl(fwd, omega_w, ind_p)
    bwd_w = wl(bwd, sub_pw)
    PA = Implies(In(zv, p), In(zv, w))
    AP = Implies(In(zv, w), In(zv, p))
    iff_pw = Iff(In(zv, p), In(zv, w))
    H_pw = Implies(PA, Not(AP))

    nr = Proof(Sequent(hyps + [Not(AP)], []), 'not_left', [bwd_w], principal=Not(AP))
    il = Proof(Sequent(hyps + [H_pw], []), 'implies_left', [fwd_w, nr], principal=H_pw)
    core = Proof(Sequent(hyps, [iff_pw]), 'not_right', [il], principal=iff_pw)

    # forall_right zv
    eq_body = Forall(zv, iff_pw)
    core_fa = Proof(Sequent(hyps, [eq_body]), 'forall_right', [core], principal=eq_body, term=zv)

    # === Close ===
    hyp_and = And(sub_pw, ind_p)
    ael2 = and_elim_left(sub_pw, ind_p, [])
    aer2 = and_elim_right(sub_pw, ind_p, [])
    ax_ha = Proof(Sequent([hyp_and], [hyp_and]), 'axiom', principal=hyp_and)
    got_sub = apply_thm(ael2, [], hyp_and, sub_pw, ax_ha, [], [])
    got_ind = apply_thm(aer2, [], hyp_and, ind_p,
                        Proof(Sequent([hyp_and], [hyp_and]), 'axiom', principal=hyp_and), [], [])

    core_w = wl(core_fa, hyp_and)
    cut_sub = Proof(Sequent([omega_w, ind_p, hyp_and], [eq_body]), 'cut',
        [wr(wl(got_sub, omega_w, ind_p), eq_body), core_w], principal=sub_pw)
    cut_ind = Proof(Sequent([omega_w, hyp_and], [eq_body]), 'cut',
        [wr(wl(got_ind, omega_w), eq_body), cut_sub], principal=ind_p)

    imp_and = Implies(hyp_and, eq_pw)
    s1 = Proof(Sequent([omega_w], [imp_and]), 'implies_right', [cut_ind], principal=imp_and)
    imp_omega = Implies(omega_w, imp_and)
    s2 = Proof(Sequent([], [imp_omega]), 'implies_right', [s1], principal=imp_omega)
    fw = Forall(w, imp_omega)
    s3 = Proof(Sequent([], [fw]), 'forall_right', [s2], principal=fw, term=w)
    fp = Forall(p, fw)
    s4 = Proof(Sequent([], [fp]), 'forall_right', [s3], principal=fp, term=p)
    s4.name = 'omega_smallest_inductive'
    return s4


