"""Theorems: logic module."""

from core.lang import Var, In, Not, Implies, Forall
from core.derived import Eq, Iff, And, Or, Exists
from core.proof import Sequent, Proof
from core import same, zfc
from tactics import wl, wr
from vocab import Empty

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
    ax_a = wr(wr(Proof(Sequent([A], [A]), 'axiom', principal=A), B), C)
    ax_c = wr(Proof(Sequent([A, C], [C]), 'axiom', principal=C), B)
    right_bc = [B] if same(B, C) else [B, C]
    impl_ac = Proof(Sequent([A, AC], right_bc), 'implies_left', [ax_a, ax_c], principal=AC)
    p0a = Proof(Sequent([AC], [NA] + right_bc), 'not_right', [impl_ac], principal=NA)
    # [AC, B] |- [B, C]
    p0b = wr(Proof(Sequent([AC, B], [B]), 'axiom', principal=B), C)
    # [AC, OrAB] |- [B, C]
    impl_or = Proof(Sequent([AC, OrAB], right_bc), 'implies_left', [p0a, p0b], principal=OrAB)
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
    andAB = And(A, B)
    s3 = Proof(Sequent([A, B], [andAB]), 'not_right', [s2], principal=andAB)
    imp1 = Implies(B, andAB)
    s4 = Proof(Sequent([A], [imp1]), 'implies_right', [s3], principal=imp1)
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
    top = Implies(And(A, B), A)
    s3 = Proof(Sequent([], [top]), 'implies_right', [s2], principal=top)
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
    top = Implies(And(A, B), B)
    s3 = Proof(Sequent([], [top]), 'implies_right', [s2], principal=top)
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



def eq_reflexive():
    """|- forall a. Eq(a, a)"""
    a = Var()
    z = Var()
    P   = In(z, a)
    PQ  = Implies(P, P)          # In(z,a) → In(z,a)
    NPQ = Not(PQ)
    H   = Implies(PQ, NPQ)       # (P→P) → ¬(P→P)
    iff_pp = Not(H)              # expanded inner body of Eq(a,a)

    # [P] |- [P]
    s1 = Proof(Sequent([P], [P]), 'axiom', principal=P)
    # [] |- [PQ]    (P → P)
    s2 = Proof(Sequent([], [PQ]), 'implies_right', [s1], principal=PQ)
    # [Not(PQ)] |-   (¬(P→P) is contradictory given P→P)
    s3 = Proof(Sequent([NPQ], []), 'not_left', [s2], principal=NPQ)
    # [H] |-         (Implies(PQ, Not(PQ)) leads to contradiction)
    s4 = Proof(Sequent([H], []), 'implies_left', [s2, s3], principal=H)
    # [] |- [iff_pp] = [] |- [Not(H)]
    s5 = Proof(Sequent([], [iff_pp]), 'not_right', [s4], principal=iff_pp)
    # [] |- [Eq(a,a)]  via forall_right: Eq(a,a) expands to Forall(z',body),
    # and with eigenvariable z the premise body[z'/z] = iff_pp is proved by s5.
    eq_aa = Eq(a, a)
    s6 = Proof(Sequent([], [eq_aa]), 'forall_right', [s5], principal=eq_aa, term=z)
    # [] |- [Forall(a, Eq(a,a))]
    fa = Forall(a, eq_aa)
    s7 = Proof(Sequent([], [fa]), 'forall_right', [s6], principal=fa, term=a)
    s7.name = 'eq_reflexive'
    return s7




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
    f1_left = [iff_pr, PR] if same(PR, RP) else [iff_pr, PR, RP]
    f1 = Proof(Sequent(f1_left, [RP]), 'axiom', principal=RP)
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
    h1_left = [iff_qs, QS] if same(QS, SQ) else [iff_qs, QS, SQ]
    h1 = Proof(Sequent(h1_left, [SQ]), 'axiom', principal=SQ)
    h2 = Proof(Sequent([iff_qs, QS], [NSQ, SQ]), 'not_right', [h1], principal=NSQ)
    h3 = Proof(Sequent([iff_qs], [H_qs, SQ]), 'implies_right', [h2], principal=H_qs)
    h4 = Proof(Sequent([H_qs], [H_qs, SQ]), 'weakening_right',
               [Proof(Sequent([H_qs], [H_qs]), 'axiom', principal=H_qs)], principal=SQ)
    h5 = Proof(Sequent([H_qs, iff_qs], [SQ]), 'not_left', [h4], principal=iff_qs)
    ext_sq = Proof(Sequent([iff_qs], [SQ]), 'cut', [h3, h5], principal=H_qs)

    # === Forward: PR, QS, or_pq |- or_rs ===
    # implies_left on PR with context G={QS, NR, P}:
    #   premise 0: G |- P, S
    a1 = Proof(Sequent([P], [P]), 'axiom', principal=P)
    a2 = wr(a1, S)
    a3 = wl(a2, NR)
    a4 = wl(a3, QS)
    #   premise 1: _set_add(G, R) |- S
    b1 = Proof(Sequent([R], [R]), 'axiom', principal=R)
    b2 = wr(b1, S)
    b3 = Proof(Sequent([NR, R], [S]), 'not_left', [b2], principal=NR)
    b4 = wl(b3, QS)
    b5 = wl(b4, P)  # no-op if P same as R
    fw_pr = Proof(Sequent([PR, QS, NR, P], [S]), 'implies_left', [a4, b5], principal=PR)
    fw_np = Proof(Sequent([PR, QS, NR], [NP, S]), 'not_right', [fw_pr], principal=NP)
    # implies_left on QS with context {PR, NR, Q}:
    c1 = Proof(Sequent([Q], [Q]), 'axiom', principal=Q)
    c2 = wr(c1, S)
    c3 = wl(c2, NR)
    c4 = wl(c3, PR)
    d1 = Proof(Sequent([S], [S]), 'axiom', principal=S)
    d2 = wl(d1, Q)   # no-op if Q same as S
    d3 = wl(d2, NR)
    d4 = wl(d3, PR)
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

    # === Backward: RP, SQ, or_rs |- or_pq ===
    # implies_left on RP with context G={SQ, NP, R}:
    #   premise 0: G |- R, Q
    aa1 = Proof(Sequent([R], [R]), 'axiom', principal=R)
    aa2 = wr(aa1, Q)
    aa3 = wl(aa2, NP)
    aa4 = wl(aa3, SQ)
    #   premise 1: _set_add(G, P) |- Q
    bb1 = Proof(Sequent([P], [P]), 'axiom', principal=P)
    bb2 = wr(bb1, Q)
    bb3 = Proof(Sequent([NP, P], [Q]), 'not_left', [bb2], principal=NP)
    bb4 = wl(bb3, SQ)
    bb5 = wl(bb4, R)  # no-op if P same as R
    bw_rp = Proof(Sequent([RP, SQ, NP, R], [Q]), 'implies_left', [aa4, bb5], principal=RP)
    bw_nr = Proof(Sequent([RP, SQ, NP], [NR, Q]), 'not_right', [bw_rp], principal=NR)
    # implies_left on SQ with context {RP, NP, S}:
    cc1 = Proof(Sequent([S], [S]), 'axiom', principal=S)
    cc2 = wr(cc1, Q)
    cc3 = wl(cc2, NP)
    cc4 = wl(cc3, RP)
    dd1 = Proof(Sequent([Q], [Q]), 'axiom', principal=Q)
    dd2 = wl(dd1, S)   # no-op if S same as Q
    dd3 = wl(dd2, NP)
    dd4 = wl(dd3, RP)
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



def char_transfer(A, B, C, vars: list[Var]):
    """|- forall vars. Iff(A,B) implies Iff(B,C) implies Iff(A,C)"""
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
    proof = Proof(Sequent([], [imp2]), 'implies_right', [s1], principal=imp2)
    for v in vars:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], principal=fa, term=v)
    return proof


