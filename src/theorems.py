"""Theorems proved from the sequent calculus. All theorems are closed (no free vars)."""

from core.lang import Var, In, Not, Implies, Forall
from core.derived import Eq, Iff, And, Or, Exists
from core.proof import Sequent, Proof
from core import zfc


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
