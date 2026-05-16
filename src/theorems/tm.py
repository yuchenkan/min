"""TM addition correctness proof.

Goal: TMReaches(delta, c0, n, cf)

Chain (each phase is LOCAL TMReaches):
  Phase1: (q0, z, tape)    →^a   (q0, a, tape)       scan past a ones
  Phase2: (q0, a, tape)    →^one (q1, sa, tape2)      write 1 over 0, move R
  Phase3: (q1, sa, tape2)  →^b   (q1, hf, tape2)      scan past b ones
  Phase4: (q1, hf, tape2)  →^one (q2, c, tape2)       read 0, write 0, move L
  Phase5: (q2, c, tape2)   →^one (qH, hf, tf)         erase last 1, move R, halt

Compose via TMReaches_compose:
  a + one = sa,  sa + b = hf,  hf + one = ssc,  ssc + one = n

TM transitions:
  q0,1 → 1,R,q0    q0,0 → 1,R,q1
  q1,1 → 1,R,q1    q1,0 → 0,L,q2
  q2,1 → 0,R,qH    q2,0 → 0,R,qH
"""

from core.lang import Var, In, Implies, Forall, Not
from core.derived import Exists, And, Or, Iff, Eq
from vocab.ordpair import OrdPair, Successor
from vocab.omega import Omega, Num
from vocab.tm import TMConfig, TMTransition, TMStep, TapeUpdate, HeadMove, TMReaches
from vocab.functions import Function as FuncDef, Apply
from vocab.sets import Empty
from vocab.recursion import Plus as PlusDef
from tm import UnaryTape, UnaryOutput


# ============================================================
# Phase result vocab — no constructor parameters
# All variables ∀-quantified, all hypotheses as implications inside
# ============================================================

class Phase1P:
    """Phase 1: scan right past a ones. a steps.
    ∀d,q0,z,a,tape,c0,c1,w,one,b.
      TMTransition(d,q0,one,one,one,q0) →
      Omega(w) → In(a,w) → Function(d) → Function(tape) →
      Num(one,1) → Num(z,0) → UnaryTape(tape,a,b) →
      TMConfig(c0,q0,z,tape) → TMConfig(c1,q0,a,tape) →
      TMReaches(d,c0,a,c1)"""
    __match_args__ = ()
    def expand(self):
        d,q0,z,a,tape = Var(postfix='_d'), Var(postfix='_q0'), Var(postfix='_z'), Var(postfix='_a'), Var(postfix='_tape')
        c0,c1 = Var(postfix='_c0'), Var(postfix='_c1')
        w,one,b = Var(postfix='_w'), Var(postfix='_one'), Var(postfix='_b')
        body = Implies(TMTransition(d,q0,one,one,one,q0),
            Implies(Omega(w), Implies(In(a,w), Implies(FuncDef(d), Implies(FuncDef(tape),
            Implies(Num(one,1), Implies(Num(z,0), Implies(UnaryTape(tape,a,b),
            Implies(TMConfig(c0,q0,z,tape), Implies(TMConfig(c1,q0,a,tape),
            TMReaches(d,c0,a,c1)))))))))))
        for v in [c1,c0,b,one,w,tape,a,z,q0,d]:
            body = Forall(v, body)
        return body
    def __str__(self): return 'Phase1P'


class Phase2P:
    """Phase 2: write 1 over separator, move R, change state. 1 step.
    ∀d,q0,q1,a,sa,one,zero,tape,tape2,c1,c2.
      TMTransition(d,q0,zero,one,one,q1) →
      Function(d) → Function(tape) →
      Num(one,1) → Num(zero,0) → Apply(tape,a,zero) →
      Successor(sa,a) → TapeUpdate(tape2,tape,a,one) →
      TMConfig(c1,q0,a,tape) → TMConfig(c2,q1,sa,tape2) →
      TMReaches(d,c1,one,c2)"""
    __match_args__ = ()
    def expand(self):
        d,q0,q1,a,sa,one = Var(postfix='_d'), Var(postfix='_q0'), Var(postfix='_q1'), Var(postfix='_a'), Var(postfix='_sa'), Var(postfix='_one')
        tape,tape2 = Var(postfix='_tape'), Var(postfix='_t2')
        c1,c2 = Var(postfix='_c1'), Var(postfix='_c2')
        zero = Var(postfix='_z')
        body = Implies(TMTransition(d,q0,zero,one,one,q1),
            Implies(FuncDef(d), Implies(FuncDef(tape),
            Implies(Num(one,1), Implies(Num(zero,0), Implies(Apply(tape,a,zero),
            Implies(Successor(sa,a), Implies(TapeUpdate(tape2,tape,a,one),
            Implies(TMConfig(c1,q0,a,tape), Implies(TMConfig(c2,q1,sa,tape2),
            TMReaches(d,c1,one,c2)))))))))))
        for v in [c2,c1,tape2,tape,zero,one,sa,a,q1,q0,d]:
            body = Forall(v, body)
        return body
    def __str__(self): return 'Phase2P'


class Phase3P:
    """Phase 3: scan right past b ones. b steps.
    ∀d,q1,sa,b,pos,tape2,c1,c2,w,one.
      TMTransition(d,q1,one,one,one,q1) →
      Omega(w) → In(b,w) → In(sa,w) →
      Function(d) → Function(tape2) →
      Num(one,1) →
      (∀p. In(p,w) → Apply(tape2,p,one)) →
      Plus(sa,b,pos) →
      TMConfig(c1,q1,sa,tape2) → TMConfig(c2,q1,pos,tape2) →
      TMReaches(d,c1,b,c2)"""
    __match_args__ = ()
    def expand(self):
        d,q1,sa,b,pos = Var(postfix='_d'), Var(postfix='_q1'), Var(postfix='_sa'), Var(postfix='_b'), Var(postfix='_pos')
        tape2 = Var(postfix='_t2')
        c1,c2 = Var(postfix='_c1'), Var(postfix='_c2')
        w,one = Var(postfix='_w'), Var(postfix='_one')
        p = Var(postfix='_p')
        pp = Var(postfix='_pp')
        tape_read = Forall(p, Implies(In(p,b), Forall(pp, Implies(PlusDef(sa,p,pp), Apply(tape2,pp,one)))))
        body = Implies(TMTransition(d,q1,one,one,one,q1),
            Implies(Omega(w), Implies(In(b,w), Implies(In(sa,w),
            Implies(FuncDef(d), Implies(FuncDef(tape2),
            Implies(Num(one,1), Implies(tape_read,
            Implies(PlusDef(sa,b,pos),
            Implies(TMConfig(c1,q1,sa,tape2), Implies(TMConfig(c2,q1,pos,tape2),
            TMReaches(d,c1,b,c2))))))))))))
        for v in [c2,c1,one,w,tape2,pos,b,sa,q1,d]:
            body = Forall(v, body)
        return body
    def __str__(self): return 'Phase3P'


class Phase4P:
    """Phase 4: read 0 past ones, write 0, move L. 1 step.
    ∀d,q1,q2,hf,c,one,zero,tape2,c1,c2.
      TMTransition(d,q1,zero,zero,zero,q2) →
      Function(d) → Function(tape2) →
      Num(one,1) → Num(zero,0) →
      Successor(hf,c) → Apply(tape2,hf,zero) →
      TMConfig(c1,q1,hf,tape2) → TMConfig(c2,q2,c,tape2) →
      TMReaches(d,c1,one,c2)"""
    __match_args__ = ()
    def expand(self):
        d,q1,q2,hf,c,one = Var(postfix='_d'), Var(postfix='_q1'), Var(postfix='_q2'), Var(postfix='_hf'), Var(postfix='_c'), Var(postfix='_one')
        zero = Var(postfix='_z')
        tape2 = Var(postfix='_t2')
        c1,c2 = Var(postfix='_c1'), Var(postfix='_c2')
        body = Implies(TMTransition(d,q1,zero,zero,zero,q2),
            Implies(FuncDef(d), Implies(FuncDef(tape2),
            Implies(Num(one,1), Implies(Num(zero,0),
            Implies(Successor(hf,c), Implies(Apply(tape2,hf,zero),
            Implies(TMConfig(c1,q1,hf,tape2), Implies(TMConfig(c2,q2,c,tape2),
            TMReaches(d,c1,one,c2))))))))))
        for v in [c2,c1,tape2,zero,one,c,hf,q2,q1,d]:
            body = Forall(v, body)
        return body
    def __str__(self): return 'Phase4P'


class Phase5P:
    """Phase 5: erase last 1, move R, halt. 1 step.
    ∀d,q2,qH,c,hf,one,zero,tape2,tf,c1,c2.
      TMTransition(d,q2,one,zero,one,qH) →
      Function(d) → Function(tape2) →
      Num(one,1) → Num(zero,0) →
      Successor(hf,c) → Apply(tape2,c,one) →
      TapeUpdate(tf,tape2,c,zero) →
      TMConfig(c1,q2,c,tape2) → TMConfig(c2,qH,hf,tf) →
      TMReaches(d,c1,one,c2)"""
    __match_args__ = ()
    def expand(self):
        d,q2,qH,c,hf,one = Var(postfix='_d'), Var(postfix='_q2'), Var(postfix='_qH'), Var(postfix='_c'), Var(postfix='_hf'), Var(postfix='_one')
        zero = Var(postfix='_z')
        tape2,tf = Var(postfix='_t2'), Var(postfix='_tf')
        c1,c2 = Var(postfix='_c1'), Var(postfix='_c2')
        body = Implies(TMTransition(d,q2,one,zero,one,qH),
            Implies(FuncDef(d), Implies(FuncDef(tape2),
            Implies(Num(one,1), Implies(Num(zero,0),
            Implies(Successor(hf,c), Implies(Apply(tape2,c,one),
            Implies(TapeUpdate(tf,tape2,c,zero),
            Implies(TMConfig(c1,q2,c,tape2), Implies(TMConfig(c2,qH,hf,tf),
            TMReaches(d,c1,one,c2)))))))))))
        for v in [c2,c1,tf,tape2,zero,one,hf,c,qH,q2,d]:
            body = Forall(v, body)
        return body
    def __str__(self): return 'Phase5P'


# ============================================================
# TMReaches_compose: chain two TMReaches via trace concatenation
# ============================================================

class TMReachesCompose:
    """TMReaches(d,x,a,y) → TMReaches(d,y,b,z) → Plus(a,b,n) →
       Omega(w) → In(a,w) → In(b,w) →
       TMReaches(d,x,n,z)"""
    __match_args__ = ()
    def expand(self):
        d = Var(postfix='_d')
        x,y,z = Var(postfix='_x'), Var(postfix='_y'), Var(postfix='_z')
        a,b,n = Var(postfix='_a'), Var(postfix='_b'), Var(postfix='_n')
        w = Var(postfix='_w')
        body = Implies(TMReaches(d,x,a,y), Implies(TMReaches(d,y,b,z),
            Implies(PlusDef(a,b,n), Implies(Omega(w), Implies(In(a,w), Implies(In(b,w),
            TMReaches(d,x,n,z)))))))
        for v in [w,n,b,a,z,y,x,d]:
            body = Forall(v, body)
        return body
    def __str__(self): return 'TMReachesCompose'


# ============================================================
# Helper theorems
# ============================================================


def tape_update_exists():
    """∃t2. TapeUpdate(t2, t, pos, val).
    [Pairing, Union, Separation] |- ∀t,pos,val. ∃t2. TapeUpdate(t2,t,pos,val)

    Construction: t2 = {z ∈ t ∪ {⟨pos,val⟩} : z=⟨pos,val⟩ ∨ (z∈t ∧ ¬∃y.z=⟨pos,y⟩)}
    From Separation on t ∪ {⟨pos,val⟩} with the TapeUpdate predicate.
    Then show z∈(t∪{⟨pos,val⟩}) is redundant given the predicate."""
    from core.lang import Var, In, Not, Implies, Forall
    from core.derived import Exists, And, Or, Iff, Eq
    from core.proof import Proof, Sequent, same
    from vocab.tm import TapeUpdate
    from vocab.ordpair import OrdPair
    from vocab.sets import Singleton, Union as UnionDef
    from tactics import apply_thm, mp, ax, fl, eir, eel, cut, wl, wr
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_intro, iff_mp, iff_mp_rev,
        or_intro_left, or_intro_right, or_elim,
        eq_substitution, eq_symmetric)
    from theorems.sets import (ordpair_exists, singleton_exists, union_exists,
        ordpair_unique)
    import core.zfc as zfc

    t = Var(postfix='t')
    pos = Var(postfix='pos')
    val = Var(postfix='val')
    t2 = Var(postfix='t2')
    zv = Var(postfix='zv')
    yv = Var(postfix='yv')

    # φ(z) = OrdPair(z,pos,val) ∨ (In(z,t) ∧ ¬∃y.OrdPair(z,pos,y))
    def phi(x):
        return Or(OrdPair(x, pos, val), And(In(x, t), Not(Exists(yv, OrdPair(x, pos, yv)))))

    # Separation: ∃t2. ∀z. z∈t2 ↔ (z∈base ∧ φ(z))
    # where base = t ∪ {⟨pos,val⟩}
    pair = Var(postfix='pair')
    sing = Var(postfix='sing')
    base = Var(postfix='base')
    op_pair = OrdPair(pair, pos, val)
    sing_pair = Singleton(sing, pair)
    union_base = UnionDef(base, t, sing)

    # Existence of pair, sing, base
    got_ex_pair = apply_thm(ordpair_exists(), [pos, val], concl=Exists(pair, op_pair))
    got_ex_sing = apply_thm(singleton_exists(), [pair], concl=Exists(sing, sing_pair))
    got_ex_base = apply_thm(union_exists(), [t, sing], concl=Exists(base, union_base))

    sep = zfc.Separation(phi, [pos, val, t, yv])
    sep_ax = Proof(Sequent([sep], [sep]), 'axiom', principal=sep)
    char_body = Iff(In(zv, t2), And(In(zv, base), phi(zv)))
    char = Forall(zv, char_body)
    got_sep = apply_thm(sep_ax, [yv, t, val, pos, base], concl=Exists(t2, char))

    # TapeUpdate body: ∀z. z∈t2 ↔ φ(z)
    tu = TapeUpdate(t2, t, pos, val)
    tu_body = tu.expand()  # ∀z'. z'∈t2 ↔ φ(z')
    tu_zv = tu_body.var  # the bound var in TapeUpdate's forall

    # Need to prove: char → tu (under [op_pair, sing_pair, union_base])
    # i.e., (z∈t2 ↔ z∈base ∧ φ(z)) → (z∈t2 ↔ φ(z))
    # Key lemma: φ(z) → z∈base
    #   Case OrdPair(z,pos,val): z=pair → z∈sing → z∈base
    #   Case In(z,t): z∈t → z∈base (union left)

    # === Prove φ(z) → z∈base ===

    # Case 1: OrdPair(zv,pos,val) → In(zv,base)
    # OrdPair(zv,pos,val) ∧ OrdPair(pair,pos,val) → Eq(zv,pair) via ordpair_unique
    ou = ordpair_unique()
    got_eq_zv_pair = apply_thm(ou, [pos, val, zv, pair])
    got_eq_zv_pair = mp(got_eq_zv_pair, ax(OrdPair(zv, pos, val)),
        OrdPair(zv, pos, val), got_eq_zv_pair.sequent.right[0].right)
    got_eq_zv_pair = mp(got_eq_zv_pair, ax(op_pair), op_pair, Eq(zv, pair))
    # [OrdPair(zv,pos,val), op_pair, Pairing] |- Eq(zv, pair)

    # Eq(zv,pair) → In(zv,sing) via Singleton characterization
    # Singleton(sing,pair): ∀x. x∈sing ↔ x=pair
    iff_zv_sing = Iff(In(zv, sing), Eq(zv, pair))
    got_iff_zv = fl(sing_pair, iff_zv_sing, zv)
    got_in_zv_sing = mp(apply_thm(iff_mp_rev(In(zv,sing), Eq(zv,pair), []), [],
        iff_zv_sing, Implies(Eq(zv,pair), In(zv,sing)), got_iff_zv),
        got_eq_zv_pair, Eq(zv,pair), In(zv,sing))
    # [OrdPair(zv,pos,val), op_pair, sing_pair, Pairing] |- In(zv, sing)

    # In(zv,sing) → In(zv,base) via Union characterization
    # Union(base,t,sing): ∀x. x∈base ↔ (x∈t ∨ x∈sing)
    or_zv_base = Or(In(zv, t), In(zv, sing))
    iff_zv_base = Iff(In(zv, base), or_zv_base)
    got_iff_zv_base = fl(union_base, iff_zv_base, zv)
    got_or_zv = apply_thm(or_intro_right(In(zv,t), In(zv,sing), []), [],
        In(zv,sing), or_zv_base, got_in_zv_sing)
    got_in_zv_base_c1 = mp(apply_thm(iff_mp_rev(In(zv,base), or_zv_base, []), [],
        iff_zv_base, Implies(or_zv_base, In(zv,base)), got_iff_zv_base),
        got_or_zv, or_zv_base, In(zv,base))
    # Case 1 done: [OrdPair(zv,pos,val), op_pair, sing_pair, union_base, Pairing] |- In(zv,base)

    # Case 2: In(zv,t) → In(zv,base) via Union (left side)
    got_or_zv_2 = apply_thm(or_intro_left(In(zv,t), In(zv,sing), []), [],
        In(zv,t), or_zv_base, ax(In(zv,t)))
    got_in_zv_base_c2 = mp(apply_thm(iff_mp_rev(In(zv,base), or_zv_base, []), [],
        iff_zv_base, Implies(or_zv_base, In(zv,base)), got_iff_zv_base),
        got_or_zv_2, or_zv_base, In(zv,base))
    # Case 2: [In(zv,t), union_base] |- In(zv,base)

    # or_elim: φ(z) → In(zv,base)
    phi_zv = phi(zv)
    oe = or_elim(OrdPair(zv,pos,val), And(In(zv,t), Not(Exists(yv, OrdPair(zv,pos,yv)))),
        In(zv,base), [])
    # Discharge case 1 hypothesis
    imp_c1 = Implies(OrdPair(zv,pos,val), In(zv,base))
    left_c1 = [f for f in got_in_zv_base_c1.sequent.left if not same(f, OrdPair(zv,pos,val))]
    got_imp_c1 = Proof(Sequent(left_c1, [imp_c1]), 'implies_right',
        [got_in_zv_base_c1], principal=imp_c1)
    # Discharge case 2: And(In(zv,t), ...) → In(zv,base)
    and_c2 = And(In(zv,t), Not(Exists(yv, OrdPair(zv,pos,yv))))
    got_in_t_from_and = apply_thm(and_elim_left(In(zv,t), Not(Exists(yv,OrdPair(zv,pos,yv))), []),
        [], and_c2, In(zv,t), ax(and_c2))
    got_in_base_from_and = cut(got_in_zv_base_c2, In(zv,t), got_in_t_from_and)
    imp_c2 = Implies(and_c2, In(zv,base))
    left_c2 = [f for f in got_in_base_from_and.sequent.left if not same(f, and_c2)]
    got_imp_c2 = Proof(Sequent(left_c2, [imp_c2]), 'implies_right',
        [got_in_base_from_and], principal=imp_c2)
    # or_elim
    got_phi_base = apply_thm(oe, [], phi_zv,
        Implies(imp_c1, Implies(imp_c2, In(zv,base))), ax(phi_zv))
    got_phi_base = mp(got_phi_base, got_imp_c1, imp_c1, Implies(imp_c2, In(zv,base)))
    got_phi_base = mp(got_phi_base, got_imp_c2, imp_c2, In(zv,base))
    # [phi_zv, op_pair, sing_pair, union_base, Pairing] |- In(zv,base)
    print(f'φ(z) → z∈base: OK')

    # === Now prove: char → TapeUpdate ===
    # char: z∈t2 ↔ (z∈base ∧ φ(z))
    # Want: z∈t2 ↔ φ(z)
    # Forward: z∈t2 → z∈base ∧ φ(z) → φ(z) (and_elim_right)
    # Backward: φ(z) → z∈base (proved above) → z∈base ∧ φ(z) → z∈t2

    and_base_phi = And(In(zv,base), phi_zv)

    # Forward: char → z∈t2 → φ(z)
    got_char_fwd = apply_thm(iff_mp(In(zv,t2), and_base_phi, []), [],
        char_body, Implies(In(zv,t2), and_base_phi), ax(char_body))
    # [char_body] |- In(zv,t2) → And(In(zv,base), φ(zv))
    got_fwd_1 = mp(got_char_fwd, ax(In(zv,t2)), In(zv,t2), and_base_phi)
    got_fwd = apply_thm(and_elim_right(In(zv,base), phi_zv, []), [],
        and_base_phi, phi_zv, got_fwd_1)
    # [char_body, In(zv,t2)] |- φ(zv)
    imp_fwd = Implies(In(zv,t2), phi_zv)
    left_fwd = [f for f in got_fwd.sequent.left if not same(f, In(zv,t2))]
    got_imp_fwd = Proof(Sequent(left_fwd, [imp_fwd]), 'implies_right', [got_fwd], principal=imp_fwd)

    # Backward: char → φ(z) → z∈t2
    got_and_base_phi = mp(apply_thm(and_intro(In(zv,base), phi_zv, []), [],
        In(zv,base), Implies(phi_zv, and_base_phi), got_phi_base),
        ax(phi_zv), phi_zv, and_base_phi)
    # [phi_zv, op_pair, sing_pair, union_base, Pairing] |- And(In(zv,base), φ(zv))
    got_char_rev = apply_thm(iff_mp_rev(In(zv,t2), and_base_phi, []), [],
        char_body, Implies(and_base_phi, In(zv,t2)), ax(char_body))
    got_bwd = mp(got_char_rev, got_and_base_phi, and_base_phi, In(zv,t2))
    # [char_body, phi_zv, op_pair, sing_pair, union_base, Pairing] |- In(zv,t2)
    imp_bwd = Implies(phi_zv, In(zv,t2))
    left_bwd = [f for f in got_bwd.sequent.left if not same(f, phi_zv)]
    got_imp_bwd = Proof(Sequent(left_bwd, [imp_bwd]), 'implies_right', [got_bwd], principal=imp_bwd)

    # Iff: z∈t2 ↔ φ(z)
    tu_iff = Iff(In(zv,t2), phi_zv)
    got_tu_iff = apply_thm(iff_intro(In(zv,t2), phi_zv, []), [],
        imp_fwd, Implies(imp_bwd, tu_iff), got_imp_fwd)
    got_tu_iff = mp(got_tu_iff, got_imp_bwd, imp_bwd, tu_iff)
    # [char_body, op_pair, sing_pair, union_base, Pairing] |- Iff(In(zv,t2), φ(zv))
    print(f'z∈t2 ↔ φ(z): OK')

    # Close ∀zv → TapeUpdate body
    fa_tu = Forall(zv, tu_iff)
    left_fa = [f for f in got_tu_iff.sequent.left if not same(f, char_body)]
    # Need to discharge char_body from left first? No — need ∀zv over the iff.
    # But char_body has zv free. Discharge it first? No, char_body = Iff(In(zv,t2), And(In(zv,base),φ(zv)))
    # which has zv free. Can't close ∀zv while char_body is on left.
    # Instead: get char_body from char (which is ∀zv. char_body) via fl.
    # Replace ax(char_body) usage with fl(char, char_body, zv).
    # Actually, I used ax(char_body) in got_char_fwd and got_char_rev.
    # Let me re-derive using fl instead.

    # Re-derive forward from char (not char_body)
    got_char_body_from_char = fl(char, char_body, zv)
    # [char] |- char_body
    got_fwd2 = apply_thm(iff_mp(In(zv,t2), and_base_phi, []), [],
        char_body, Implies(In(zv,t2), and_base_phi), got_char_body_from_char)
    got_fwd2 = mp(got_fwd2, ax(In(zv,t2)), In(zv,t2), and_base_phi)
    got_fwd2 = apply_thm(and_elim_right(In(zv,base), phi_zv, []), [],
        and_base_phi, phi_zv, got_fwd2)
    imp_fwd2 = Implies(In(zv,t2), phi_zv)
    left_fwd2 = [f for f in got_fwd2.sequent.left if not same(f, In(zv,t2))]
    got_imp_fwd2 = Proof(Sequent(left_fwd2, [imp_fwd2]), 'implies_right', [got_fwd2], principal=imp_fwd2)

    # Re-derive backward from char
    got_char_body_from_char2 = fl(char, char_body, zv)
    got_char_rev2 = apply_thm(iff_mp_rev(In(zv,t2), and_base_phi, []), [],
        char_body, Implies(and_base_phi, In(zv,t2)), got_char_body_from_char2)
    got_bwd2 = mp(got_char_rev2, got_and_base_phi, and_base_phi, In(zv,t2))
    imp_bwd2 = Implies(phi_zv, In(zv,t2))
    left_bwd2 = [f for f in got_bwd2.sequent.left if not same(f, phi_zv)]
    got_imp_bwd2 = Proof(Sequent(left_bwd2, [imp_bwd2]), 'implies_right', [got_bwd2], principal=imp_bwd2)

    got_tu_iff2 = apply_thm(iff_intro(In(zv,t2), phi_zv, []), [],
        imp_fwd2, Implies(imp_bwd2, tu_iff), got_imp_fwd2)
    got_tu_iff2 = mp(got_tu_iff2, got_imp_bwd2, imp_bwd2, tu_iff)
    # [char, op_pair, sing_pair, union_base, Pairing] |- Iff(In(zv,t2), φ(zv))

    # Close ∀zv — char doesn't have zv free (it's ∀zv. ...)
    fa_tu2 = Forall(zv, tu_iff)
    got_fa_tu = Proof(Sequent(got_tu_iff2.sequent.left, [fa_tu2]),
        'forall_right', [got_tu_iff2], principal=fa_tu2, term=zv)
    # [char, op_pair, sing_pair, union_base, Pairing] |- ∀zv. z∈t2 ↔ φ(z) = TapeUpdate(t2,...)

    # Bridge to TapeUpdate vocab
    got_tu = cut(ax(tu), tu, got_fa_tu)
    # eir t2
    got_ex_tu = eir(got_tu, tu, t2, t2)
    # eel t2 from char
    got_ex_tu = eel(got_ex_tu, char, t2)
    got_ex_tu = cut(got_ex_tu, Exists(t2, char), got_sep)
    # eel base from union_base
    got_ex_tu = eel(got_ex_tu, union_base, base)
    got_ex_tu = cut(got_ex_tu, Exists(base, union_base), got_ex_base)
    # eel sing from sing_pair
    got_ex_tu = eel(got_ex_tu, sing_pair, sing)
    got_ex_tu = cut(got_ex_tu, Exists(sing, sing_pair), got_ex_sing)
    # eel pair from op_pair
    got_ex_tu = eel(got_ex_tu, op_pair, pair)
    got_ex_tu = cut(got_ex_tu, Exists(pair, op_pair), got_ex_pair)

    # Close ∀
    proof = got_ex_tu
    for v in [val, pos, t]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'tape_update_exists'
    return proof





def config_intro():
    """Construct TMConfig from OrdPair witnesses.
    Pairing |- forall c, q, h, t, inner.
        OrdPair(inner, h, t) -> OrdPair(c, q, inner) -> TMConfig(c, q, h, t)

    TMConfig(c,q,h,t) = forall inner'. OrdPair(inner',h,t) -> OrdPair(c,q,inner').
    Proof: from OrdPair(inner,h,t) and any OrdPair(inner',h,t), by ordpair_unique
    get Eq(inner',inner). Then ordpair_set_transfer gives OrdPair(c,q,inner')."""
    from tactics import apply_thm, mp, ax, wl
    from core.proof import Proof, Sequent, same
    from theorems.sets import ordpair_unique, ordpair_set_transfer
    import theorems

    c, q, h, t, inner, inner2 = Var(), Var(), Var(), Var(), Var(), Var()

    op_inner = OrdPair(inner, h, t)
    op_inner2 = OrdPair(inner2, h, t)
    op_c = OrdPair(c, q, inner)
    op_c2 = OrdPair(c, q, inner2)
    cfg = TMConfig(c, q, h, t)  # = Forall(inner', OrdPair(inner',h,t) -> OrdPair(c,q,inner'))

    # ordpair_unique: OrdPair(inner2,h,t) -> OrdPair(inner,h,t) -> Eq(inner2,inner)
    ou = ordpair_unique()
    eq_i2_i = Eq(inner2, inner)
    got_eq = mp(apply_thm(ou, [h, t, inner2, inner], op_inner2,
        Implies(op_inner, eq_i2_i), ax(op_inner2)),
        ax(op_inner), op_inner, eq_i2_i)
    # [op_inner2, op_inner] |- Eq(inner2, inner)

    # ordpair_set_transfer: Eq(inner2,inner) -> OrdPair(c,q,inner) -> OrdPair(c,q,inner2)
    # Wait, ordpair_set_transfer is: Eq(a,b) -> OrdPair(b,c,d) -> OrdPair(a,c,d)
    # I need: Eq(inner2, inner) -> OrdPair(c, q, inner) -> OrdPair(c, q, inner2)
    # That's ordpair_eq_transfer or ordpair_val_transfer... let me check
    # ordpair_set_transfer: Eq(a,b) -> OrdPair(b,c,d) -> OrdPair(a,c,d)
    # I need to transfer the THIRD argument, not the first.
    # ordpair_eq_transfer: Eq(a,c) -> Eq(b,d) -> OrdPair(t,a,b) -> OrdPair(t,c,d)
    # With a=q, c=q (Eq(q,q)), b=inner2, d=inner... no, I need OrdPair(c,q,inner2) from
    # Eq(inner2,inner) and OrdPair(c,q,inner)
    # That's: Eq(inner2, inner) means inner2 = inner. OrdPair(c, q, inner) + Eq(inner, inner2)?
    # I need eq_symmetric first: Eq(inner2, inner) -> Eq(inner, inner2)
    # Then ordpair_val_transfer: Eq(b,c) -> OrdPair(t,a,b) -> OrdPair(t,a,c)
    # gives: Eq(inner, inner2) -> OrdPair(c,q,inner) -> OrdPair(c,q,inner2) ✓
    from theorems.logic import eq_symmetric
    ost = theorems.ordpair_val_transfer()
    eq_sym = eq_symmetric()
    eq_i_i2 = Eq(inner, inner2)

    got_eq_rev = apply_thm(eq_sym, [inner2, inner], eq_i2_i, eq_i_i2, got_eq)
    # [op_inner2, op_inner] |- Eq(inner, inner2)

    got_op_c2 = mp(apply_thm(ost, [c, q, inner, inner2], eq_i_i2,
        Implies(op_c, op_c2), got_eq_rev), ax(op_c), op_c, op_c2)
    # [op_inner2, op_inner, op_c] |- OrdPair(c, q, inner2)

    # Close: implies_right for op_inner2, then forall_right for inner2 → gives TMConfig body
    imp = Implies(op_inner2, op_c2)
    left = [f for f in got_op_c2.sequent.left if not same(f, op_inner2)]
    p = Proof(Sequent(left, [imp]), 'implies_right', [got_op_c2], principal=imp)
    # [op_inner, op_c] |- Implies(OrdPair(inner2,h,t), OrdPair(c,q,inner2))

    fa = Forall(inner2, imp)
    p = Proof(Sequent(p.sequent.left, [fa]), 'forall_right', [p], principal=fa, term=inner2)
    # [op_inner, op_c] |- Forall(inner2, OrdPair(inner2,h,t) -> OrdPair(c,q,inner2)) = TMConfig

    # Close outer implications and foralls
    for premise in [op_c, op_inner]:
        imp_outer = Implies(premise, p.sequent.right[0])
        left = [f for f in p.sequent.left if not same(f, premise)]
        p = Proof(Sequent(left, [imp_outer]), 'implies_right', [p], principal=imp_outer)

    proof = p
    for v in [inner, t, h, q, c]:
        body = proof.sequent.right[0]
        fa_v = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa_v]), 'forall_right',
            [proof], principal=fa_v, term=v)

    proof.name = 'config_intro'
    return proof



def tape_update_function():
    """TapeUpdate preserves Function.
    |- ∀t2,t,pos,val. TapeUpdate(t2,t,pos,val) → Function(t) → Function(t2)"""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from core.proof import Proof, Sequent, same
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        or_elim, iff_mp, iff_mp_rev, eq_symmetric, eq_reflexive)
    from theorems.omega import func_unique_thm
    from theorems.sets import ordpair_exists, tuple_injection, ordpair_unique
    from vocab.functions import Function as FuncDef, Apply, Relation as RelDef
    from vocab.tm import TapeUpdate
    from vocab.ordpair import OrdPair
    from core.proof import Proof, Sequent, same
    from core.lang import Var, In, Not, Implies, Forall
    from core.derived import Eq, And, Or, Iff, Exists

    t2 = Var(postfix='t2')
    t = Var(postfix='t')
    pos = Var(postfix='pos')
    val = Var(postfix='val')
    tu = TapeUpdate(t2, t, pos, val)
    func_t = FuncDef(t)

    # TapeUpdate expansion: ∀bv. bv∈t2 ↔ (OrdPair(bv,pos,val) ∨ (bv∈t ∧ ¬∃y.OrdPair(bv,pos,y)))
    tu_exp = tu.expand()
    bv = tu_exp.var
    iff_body = tu_exp.body
    print(f'tape_update_function: tu bv={bv}, iff_body left={iff_body.left}')

    # === Part 1: Relation(t2) ===
    zv = Var(postfix='zv')
    xv = Var(postfix='xv')
    yv = Var(postfix='yv')
    op_z = OrdPair(zv, xv, yv)
    ex_xy = Exists(xv, Exists(yv, op_z))

    # Instantiate TapeUpdate at zv
    iff_at_z = iff_body.subst(bv, zv)
    got_iff_z = fl(tu, iff_at_z, zv)
    or_z = iff_at_z.right
    got_fwd_z = mp(apply_thm(iff_mp(iff_at_z.left, or_z, []), [],
        iff_at_z, Implies(iff_at_z.left, or_z), got_iff_z),
        ax(In(zv, t2)), In(zv, t2), or_z)
    # [tu, In(zv,t2)] |- Or(OrdPair(zv,pos,val), And(In(zv,t), Not(...)))
    print(f'tape_update_function: fwd done, or_z.left={or_z.left}')

    # Case 1: OrdPair(zv,pos,val) → ∃x,y. OrdPair(zv,x,y)
    op_zpv = or_z.left  # OrdPair(zv,pos,val) from TapeUpdate expansion
    # Build ∃y.OrdPair(zv,pos,y) then ∃x.∃y.OrdPair(zv,x,y) using op_zpv's structure
    op_z_at_pos = OrdPair(zv, pos, yv)  # template for eir
    got_c1 = eir(ax(op_zpv), op_z_at_pos, yv, val)  # ∃y. OrdPair(zv,pos,y)
    got_c1 = eir(got_c1, Exists(yv, OrdPair(zv, xv, yv)), xv, pos)  # ∃x.∃y. OrdPair(zv,x,y)

    # Case 2: And(In(zv,t), ...) → z∈t → Relation(t) → ∃x,y. OrdPair(zv,x,y)
    and_z = or_z.right
    got_in_zt = apply_thm(and_elim_left(and_z.left, and_z.right, []), [],
        and_z, and_z.left, ax(and_z))
    # Relation(t) from Function(t)
    func_exp = func_t.expand()
    rel_t = func_exp.left
    got_rel = apply_thm(and_elim_left(rel_t, func_exp.right, []), [],
        func_t, rel_t, ax(func_t))
    # Instantiate Relation at zv
    rel_exp = rel_t.expand()
    imp_rel_z = rel_exp.body.subst(rel_exp.var, zv)
    got_rel_inst = fl(rel_t, imp_rel_z, zv)
    got_c2_inner = mp(got_rel_inst, got_in_zt, imp_rel_z.left, imp_rel_z.right)
    got_c2 = cut(ax(ex_xy), ex_xy, got_c2_inner)

    # Or_elim
    oe = or_elim(op_zpv, and_z, ex_xy, [])
    got_or_ex = apply_thm(oe, [], or_z,
        Implies(Implies(op_zpv, ex_xy), Implies(Implies(and_z, ex_xy), ex_xy)),
        got_fwd_z)
    imp_c1 = Implies(op_zpv, ex_xy)
    left_c1 = [f for f in got_c1.sequent.left if not same(f, op_zpv)]
    got_c1_imp = Proof(Sequent(left_c1, [imp_c1]), 'implies_right', [got_c1], principal=imp_c1)
    got_or_ex = mp(got_or_ex, got_c1_imp, imp_c1, got_or_ex.sequent.right[0].right)
    imp_c2 = Implies(and_z, ex_xy)
    left_c2 = [f for f in got_c2.sequent.left if not same(f, and_z)]
    got_c2_imp = Proof(Sequent(left_c2, [imp_c2]), 'implies_right', [got_c2], principal=imp_c2)
    got_or_ex = mp(got_or_ex, got_c2_imp, imp_c2, ex_xy)

    # Discharge In(zv,t2), close ∀zv → Relation(t2)
    imp_in = Implies(In(zv, t2), ex_xy)
    left_in = [f for f in got_or_ex.sequent.left if not same(f, In(zv, t2))]
    got_rel_t2 = Proof(Sequent(left_in, [imp_in]), 'implies_right', [got_or_ex], principal=imp_in)
    got_rel_t2 = Proof(Sequent(got_rel_t2.sequent.left, [Forall(zv, imp_in)]),
        'forall_right', [got_rel_t2], principal=Forall(zv, imp_in), term=zv)
    rel_t2 = RelDef(t2)
    got_rel_t2 = cut(ax(rel_t2), rel_t2, got_rel_t2)
    print(f'tape_update_function: Relation(t2) done')

    # === Part 2: SingleValued(t2) ===
    # ∀a,b1,b2. And(Apply(t2,a,b1), Apply(t2,a,b2)) → Eq(b1,b2)
    # Apply(t2,a,b) = ∃p. OrdPair(p,a,b) ∧ In(p,t2)
    # In(p,t2) from TapeUpdate: OrdPair(p,pos,val) ∨ (In(p,t) ∧ ¬∃y.OrdPair(p,pos,y))
    # Case analysis: for each Apply, either a=pos (value is val) or a≠pos (value from t).
    # 4 cases total, but they reduce to: same a → same b.
    # This is the standard proof that Separation-based update preserves single-valuedness.

    av = Var(postfix='av')
    b1 = Var(postfix='b1')
    b2 = Var(postfix='b2')
    p1v = Var(postfix='p1')
    p2v = Var(postfix='p2')
    app1 = Apply(t2, av, b1)
    app2 = Apply(t2, av, b2)
    eq_b = Eq(b1, b2)

    # Open Apply(t2,av,b1): ∃p1. OrdPair(p1,av,b1) ∧ In(p1,t2)
    op1 = OrdPair(p1v, av, b1)
    in_p1 = In(p1v, t2)
    and_app1 = And(op1, in_p1)

    # Open Apply(t2,av,b2): ∃p2. OrdPair(p2,av,b2) ∧ In(p2,t2)
    op2 = OrdPair(p2v, av, b2)
    in_p2 = In(p2v, t2)
    and_app2 = And(op2, in_p2)

    # From In(p1,t2) via TapeUpdate fwd: Or(OrdPair(p1,pos,val), And(In(p1,t), ...))
    iff_p1 = iff_body.subst(bv, p1v)
    got_iff_p1 = fl(tu, iff_p1, p1v)
    got_or_p1 = mp(apply_thm(iff_mp(iff_p1.left, iff_p1.right, []), [],
        iff_p1, Implies(iff_p1.left, iff_p1.right), got_iff_p1),
        apply_thm(and_elim_right(op1, in_p1, []), [], and_app1, in_p1, ax(and_app1)),
        in_p1, iff_p1.right)

    iff_p2 = iff_body.subst(bv, p2v)
    got_iff_p2 = fl(tu, iff_p2, p2v)
    got_or_p2 = mp(apply_thm(iff_mp(iff_p2.left, iff_p2.right, []), [],
        iff_p2, Implies(iff_p2.left, iff_p2.right), got_iff_p2),
        apply_thm(and_elim_right(op2, in_p2, []), [], and_app2, in_p2, ax(and_app2)),
        in_p2, iff_p2.right)
    print(f'tape_update_function: opened Apply components')

    # SingleValued: from or_p1, or_p2, derive Eq(b1,b2) using 4-case or_elim.
    # or_p1.left = OrdPair(p1,pos,val), or_p1.right = And(In(p1,t), Not(∃y.OrdPair(p1,pos,y)))
    # or_p2.left = OrdPair(p2,pos,val), or_p2.right = And(In(p2,t), Not(∃y.OrdPair(p2,pos,y)))
    or_p1_body = iff_p1.right
    or_p2_body = iff_p2.right
    op1_pv = or_p1_body.left   # OrdPair(p1,pos,val)
    and1_t = or_p1_body.right  # And(In(p1,t), Not(...))
    op2_pv = or_p2_body.left   # OrdPair(p2,pos,val)
    and2_t = or_p2_body.right  # And(In(p2,t), Not(...))

    from theorems.logic import eq_transitive

    # tuple_injection: OrdPair(p,a,b) → OrdPair(p,c,d) → And(Eq(a,c), Eq(b,d))
    ti = tuple_injection()

    # Helper: derive Eq(b_i, val) from OrdPair(pi,av,bi) + OrdPair(pi,pos,val)
    def val_from_pair(pi, bi, opi_ab, opi_pv):
        """[opi_ab, opi_pv] |- Eq(bi, val)"""
        got_ti = apply_thm(ti, [av, bi, pos, val, pi])
        imp_cur = got_ti.sequent.right[0]
        got_ti = mp(got_ti, ax(opi_ab), imp_cur.left, imp_cur.right)
        imp_cur = got_ti.sequent.right[0]
        got_ti = mp(got_ti, ax(opi_pv), imp_cur.left, imp_cur.right)
        # And(Eq(av,pos), Eq(bi,val))
        return apply_thm(and_elim_right(Eq(av, pos), Eq(bi, val), []), [],
            got_ti.sequent.right[0], Eq(bi, val), got_ti)

    # Helper: derive contradiction from OrdPair(pi,av,bi) + OrdPair(pi,pos,val) + Not(∃y.OrdPair(pi,pos,y))
    def contradiction_from_pair(pi, bi, opi_ab, opi_pv, not_ex):
        """[opi_ab, opi_pv, not_ex] |- anything (contradiction)"""
        # From OrdPair(pi,av,bi) + OrdPair(pi,pos,val) → Eq(av,pos)
        got_ti = apply_thm(ti, [av, bi, pos, val, pi])
        got_ti = mp(got_ti, ax(opi_ab), opi_ab, got_ti.sequent.right[0].right)
        got_ti = mp(got_ti, ax(opi_pv), opi_pv, got_ti.sequent.right[0])
        # got_ti has And(Eq(av,pos), Eq(bi,val)) but we don't need it.
        # We need: ∃y.OrdPair(pi,pos,y) to contradict not_ex.
        # OrdPair(pi,pos,val) → eir y=val → ∃y.OrdPair(pi,pos,y)
        yv2 = Var(postfix='yv2')
        op_pi_pos_y = OrdPair(pi, pos, yv2)
        got_ex = eir(ax(opi_pv), op_pi_pos_y, yv2, val)
        # not_left: from got_ex |- ∃y.OrdPair(pi,pos,y) and not_ex on left → bottom
        ex_formula = got_ex.sequent.right[0]
        return got_ex  # We'll use not_left later

    # Case (1,1): op1_pv ∧ op2_pv → Eq(b1,val) ∧ Eq(b2,val) → Eq(b1,b2)
    got_eq_b1v = val_from_pair(p1v, b1, op1, op1_pv)
    got_eq_b2v = val_from_pair(p2v, b2, op2, op2_pv)
    # Eq(b1,val) ∧ Eq(b2,val) → Eq(b1,b2) via eq_symmetric + eq_transitive
    es = eq_symmetric()
    et = eq_transitive()
    got_eq_vb2 = apply_thm(es, [b2, val], Eq(b2, val), Eq(val, b2), got_eq_b2v)
    got_eq_b1b2 = apply_thm(et, [b1, val, b2])
    got_eq_b1b2 = mp(got_eq_b1b2, got_eq_b1v, Eq(b1, val), got_eq_b1b2.sequent.right[0].right)
    got_eq_b1b2 = mp(got_eq_b1b2, got_eq_vb2, Eq(val, b2), eq_b)
    got_case11 = got_eq_b1b2
    # [op1, op1_pv, op2, op2_pv] |- Eq(b1,b2)
    print(f'tape_update_function: case(1,1) done')

    # Case (2,2): and1_t ∧ and2_t → Apply(t,av,b1) ∧ Apply(t,av,b2) → Eq(b1,b2)
    in_p1_t = apply_thm(and_elim_left(and1_t.left, and1_t.right, []), [],
        and1_t, and1_t.left, ax(and1_t))
    in_p2_t = apply_thm(and_elim_left(and2_t.left, and2_t.right, []), [],
        and2_t, and2_t.left, ax(and2_t))
    # Apply(t,av,b1) = ∃p. OrdPair(p,av,b1) ∧ In(p,t). Witness p=p1.
    app_t_b1 = Apply(t, av, b1)
    app_t_b2 = Apply(t, av, b2)
    papp1 = Var(postfix='pa1')
    got_app_t1 = eir(
        mp(apply_thm(and_intro(op1, in_p1_t.sequent.right[0], []), [],
            op1, Implies(in_p1_t.sequent.right[0], And(op1, in_p1_t.sequent.right[0])), ax(op1)),
            in_p1_t, in_p1_t.sequent.right[0], And(op1, in_p1_t.sequent.right[0])),
        And(OrdPair(papp1, av, b1), In(papp1, t)), papp1, p1v)
    got_app_t1 = cut(ax(app_t_b1), app_t_b1, got_app_t1)
    papp2 = Var(postfix='pa2')
    got_app_t2 = eir(
        mp(apply_thm(and_intro(op2, in_p2_t.sequent.right[0], []), [],
            op2, Implies(in_p2_t.sequent.right[0], And(op2, in_p2_t.sequent.right[0])), ax(op2)),
            in_p2_t, in_p2_t.sequent.right[0], And(op2, in_p2_t.sequent.right[0])),
        And(OrdPair(papp2, av, b2), In(papp2, t)), papp2, p2v)
    got_app_t2 = cut(ax(app_t_b2), app_t_b2, got_app_t2)
    # func_unique on t: Apply(t,av,b1) ∧ Apply(t,av,b2) → Eq(b1,b2)
    fu = func_unique_thm()
    got_fu = apply_thm(fu, [t, av, b1, b2])
    got_fu = mp(got_fu, ax(func_t), func_t, got_fu.sequent.right[0].right)
    got_fu = mp(got_fu, got_app_t1, app_t_b1, got_fu.sequent.right[0].right)
    got_case22 = mp(got_fu, got_app_t2, app_t_b2, eq_b)
    # [and1_t, and2_t, op1, op2, Function(t)] |- Eq(b1,b2)
    print(f'tape_update_function: case(2,2) done')

    # Case (1,2): op1_pv ∧ and2_t → contradiction → Eq(b1,b2)
    # OrdPair(p1,pos,val) → tuple_injection with OrdPair(p1,av,b1) → Eq(av,pos)
    # OrdPair(p2,av,b2) with Eq(av,pos) → OrdPair(p2,pos,b2) → ∃y.OrdPair(p2,pos,y)
    # But and2_t has Not(∃y.OrdPair(p2,pos,y)) → contradiction.
    # From contradiction: Eq(b1,b2) by weakening.

    # Eq(av,pos) from tuple_injection
    got_ti_12 = apply_thm(ti, [av, b1, pos, val, p1v])
    imp_cur = got_ti_12.sequent.right[0]
    got_ti_12 = mp(got_ti_12, ax(op1), imp_cur.left, imp_cur.right)
    imp_cur = got_ti_12.sequent.right[0]
    got_ti_12 = mp(got_ti_12, ax(op1_pv), imp_cur.left, imp_cur.right)
    got_eq_ap = apply_thm(and_elim_left(Eq(av,pos), Eq(b1,val), []), [],
        got_ti_12.sequent.right[0], Eq(av,pos), got_ti_12)
    # OrdPair(p2,av,b2) + Eq(av,pos) → OrdPair(p2,pos,b2) via ordpair_eq_transfer
    from theorems.sets import ordpair_eq_transfer
    oet = ordpair_eq_transfer()
    op2_pos_b2 = OrdPair(p2v, pos, b2)
    got_op2_pb = apply_thm(oet, [av, b2, pos, b2, p2v])
    got_op2_pb = mp(got_op2_pb, got_eq_ap, Eq(av,pos), got_op2_pb.sequent.right[0].right)
    got_eq_b2b2 = apply_thm(eq_reflexive(), [b2])
    got_op2_pb = mp(got_op2_pb, got_eq_b2b2, Eq(b2,b2), got_op2_pb.sequent.right[0].right)
    got_op2_pb = mp(got_op2_pb, ax(op2), op2, op2_pos_b2)
    # ∃y.OrdPair(p2,pos,y)
    yv3 = Var(postfix='yv3')
    op2_pos_y = OrdPair(p2v, pos, yv3)
    got_ex_p2 = eir(got_op2_pb, op2_pos_y, yv3, b2)
    # Not(∃y.OrdPair(p2,pos,y)) from and2_t
    not_ex_p2 = and2_t.right  # Not(∃y.OrdPair(p2,pos,y))
    got_not_ex = apply_thm(and_elim_right(and2_t.left, not_ex_p2, []), [],
        and2_t, not_ex_p2, ax(and2_t))
    # Contradiction: not_left on got_ex_p2, then weakening_right for eq_b
    ex_p2_formula = got_ex_p2.sequent.right[0]
    # Merge contexts
    all_ctx_12 = list(got_ex_p2.sequent.left)
    for f in got_not_ex.sequent.left:
        if not any(same(f, g) for g in all_ctx_12):
            all_ctx_12.append(f)
    # not_left: [ctx, Not(ex)] |- (empty). Then wr to add eq_b. Then cut Not(ex).
    got_contra = Proof(Sequent(all_ctx_12 + [not_ex_p2], []),
        'not_left', [weaken_to(got_ex_p2, all_ctx_12)], principal=not_ex_p2)
    got_contra = wr(got_contra, eq_b)  # [ctx, Not(ex)] |- eq_b
    got_case12 = cut(got_contra, not_ex_p2, weaken_to(got_not_ex, all_ctx_12))
    # [op1, op1_pv, op2, and2_t] |- Eq(b1,b2) (from contradiction)
    print(f'tape_update_function: case(1,2) done')

    # Case (2,1): symmetric — and1_t ∧ op2_pv → contradiction → Eq(b1,b2)
    got_ti_21 = apply_thm(ti, [av, b2, pos, val, p2v])
    imp_cur = got_ti_21.sequent.right[0]
    got_ti_21 = mp(got_ti_21, ax(op2), imp_cur.left, imp_cur.right)
    imp_cur = got_ti_21.sequent.right[0]
    got_ti_21 = mp(got_ti_21, ax(op2_pv), imp_cur.left, imp_cur.right)
    got_eq_ap2 = apply_thm(and_elim_left(Eq(av,pos), Eq(b2,val), []), [],
        got_ti_21.sequent.right[0], Eq(av,pos), got_ti_21)
    op1_pos_b1 = OrdPair(p1v, pos, b1)
    got_op1_pb = apply_thm(oet, [av, b1, pos, b1, p1v])
    got_op1_pb = mp(got_op1_pb, got_eq_ap2, Eq(av,pos), got_op1_pb.sequent.right[0].right)
    got_eq_b1b1 = apply_thm(eq_reflexive(), [b1])
    got_op1_pb = mp(got_op1_pb, got_eq_b1b1, Eq(b1,b1), got_op1_pb.sequent.right[0].right)
    got_op1_pb = mp(got_op1_pb, ax(op1), op1, op1_pos_b1)
    yv4 = Var(postfix='yv4')
    op1_pos_y = OrdPair(p1v, pos, yv4)
    got_ex_p1 = eir(got_op1_pb, op1_pos_y, yv4, b1)
    not_ex_p1 = and1_t.right
    got_not_ex1 = apply_thm(and_elim_right(and1_t.left, not_ex_p1, []), [],
        and1_t, not_ex_p1, ax(and1_t))
    ex_p1_formula = got_ex_p1.sequent.right[0]
    all_ctx_21 = list(got_ex_p1.sequent.left)
    for f in got_not_ex1.sequent.left:
        if not any(same(f, g) for g in all_ctx_21):
            all_ctx_21.append(f)
    got_contra2 = Proof(Sequent(all_ctx_21 + [not_ex_p1], []),
        'not_left', [weaken_to(got_ex_p1, all_ctx_21)], principal=not_ex_p1)
    got_contra2 = wr(got_contra2, eq_b)
    got_case21 = cut(got_contra2, not_ex_p1, weaken_to(got_not_ex1, all_ctx_21))
    print(f'tape_update_function: case(2,1) done')

    # === 4-case or_elim ===
    # or_p1: [tu, and_app1] |- Or(op1_pv, and1_t)
    # or_p2: [tu, and_app2] |- Or(op2_pv, and2_t)
    # Need: [tu, and_app1, and_app2, func_t, op1, op2] |- Eq(b1,b2)

    # Inner or_elim on or_p2 for each case of or_p1:
    # Case or_p1=op1_pv: or_elim(or_p2, op2_pv→case11, and2_t→case12) → Eq(b1,b2)
    oe2 = or_elim(op2_pv, and2_t, eq_b, [])
    # case11: [op1, op1_pv, op2, op2_pv] |- eq_b
    # case12: [op1, op1_pv, op2, and2_t] |- eq_b
    imp_c11 = Implies(op2_pv, eq_b)
    left_c11 = [f for f in got_case11.sequent.left if not same(f, op2_pv)]
    got_c11_imp = Proof(Sequent(left_c11, [imp_c11]), 'implies_right', [got_case11], principal=imp_c11)
    imp_c12 = Implies(and2_t, eq_b)
    left_c12 = [f for f in got_case12.sequent.left if not same(f, and2_t)]
    got_c12_imp = Proof(Sequent(left_c12, [imp_c12]), 'implies_right', [got_case12], principal=imp_c12)

    got_inner1 = apply_thm(oe2, [], or_p2_body,
        Implies(imp_c11, Implies(imp_c12, eq_b)), ax(or_p2_body))
    got_inner1 = mp(got_inner1, got_c11_imp, imp_c11, Implies(imp_c12, eq_b))
    got_inner1 = mp(got_inner1, got_c12_imp, imp_c12, eq_b)
    # [or_p2_body, op1, op1_pv, op2, Function(t)] |- Eq(b1,b2)

    # Case or_p1=and1_t: or_elim(or_p2, op2_pv→case21, and2_t→case22) → Eq(b1,b2)
    imp_c21 = Implies(op2_pv, eq_b)
    left_c21 = [f for f in got_case21.sequent.left if not same(f, op2_pv)]
    got_c21_imp = Proof(Sequent(left_c21, [imp_c21]), 'implies_right', [got_case21], principal=imp_c21)
    imp_c22 = Implies(and2_t, eq_b)
    left_c22 = [f for f in got_case22.sequent.left if not same(f, and2_t)]
    got_c22_imp = Proof(Sequent(left_c22, [imp_c22]), 'implies_right', [got_case22], principal=imp_c22)

    got_inner2 = apply_thm(oe2, [], or_p2_body,
        Implies(imp_c21, Implies(imp_c22, eq_b)), ax(or_p2_body))
    got_inner2 = mp(got_inner2, got_c21_imp, imp_c21, Implies(imp_c22, eq_b))
    got_inner2 = mp(got_inner2, got_c22_imp, imp_c22, eq_b)
    # [or_p2_body, op1, and1_t, op2, Function(t)] |- Eq(b1,b2)

    # Outer or_elim on or_p1:
    oe1 = or_elim(op1_pv, and1_t, eq_b, [])
    imp_i1 = Implies(op1_pv, eq_b)
    left_i1 = [f for f in got_inner1.sequent.left if not same(f, op1_pv)]
    got_i1_imp = Proof(Sequent(left_i1, [imp_i1]), 'implies_right', [got_inner1], principal=imp_i1)
    imp_i2 = Implies(and1_t, eq_b)
    left_i2 = [f for f in got_inner2.sequent.left if not same(f, and1_t)]
    got_i2_imp = Proof(Sequent(left_i2, [imp_i2]), 'implies_right', [got_inner2], principal=imp_i2)

    got_sv_result = apply_thm(oe1, [], or_p1_body,
        Implies(imp_i1, Implies(imp_i2, eq_b)), ax(or_p1_body))
    got_sv_result = mp(got_sv_result, got_i1_imp, imp_i1, Implies(imp_i2, eq_b))
    got_sv_result = mp(got_sv_result, got_i2_imp, imp_i2, eq_b)
    # [or_p1_body, or_p2_body, op1, op2, Function(t)] |- Eq(b1,b2)

    # Cut or_p1_body and or_p2_body with got_or_p1 and got_or_p2
    got_sv_result = cut(got_sv_result, or_p1_body, got_or_p1)
    got_sv_result = cut(got_sv_result, or_p2_body, got_or_p2)
    # [tu, and_app1, and_app2, op1, op2, Function(t)] |- Eq(b1,b2)

    # Cut op1 and op2 from and_app1 and and_app2 (they were ax'd separately)
    got_op1_from_and = apply_thm(and_elim_left(op1, in_p1, []), [], and_app1, op1, ax(and_app1))
    got_op2_from_and = apply_thm(and_elim_left(op2, in_p2, []), [], and_app2, op2, ax(and_app2))
    if any(same(op1, f) for f in got_sv_result.sequent.left):
        got_sv_result = cut(got_sv_result, op1, got_op1_from_and)
    if any(same(op2, f) for f in got_sv_result.sequent.left):
        got_sv_result = cut(got_sv_result, op2, got_op2_from_and)
    # eel p1v from and_app1, p2v from and_app2. Cut with app1, app2.
    got_sv_result = eel(got_sv_result, and_app1, p1v)
    got_sv_result = cut(got_sv_result, app1, ax(app1))
    got_sv_result = eel(got_sv_result, and_app2, p2v)
    got_sv_result = cut(got_sv_result, app2, ax(app2))
    print(f'tape_update_function: SingleValued core done')

    # Discharge Apply(t2,av,b1), Apply(t2,av,b2), close ∀av,b1,b2
    # SingleValued = ∀a,b1,b2. And(Apply(t2,a,b1), Apply(t2,a,b2)) → Eq(b1,b2)
    and_apps = And(app1, app2)
    got_sv_from_and = mp(apply_thm(and_intro(app1, app2, []), [],
        app1, Implies(app2, and_apps), ax(app1)), ax(app2), app2, and_apps)
    got_sv_result = cut(got_sv_result, app1,
        apply_thm(and_elim_left(app1, app2, []), [], and_apps, app1, ax(and_apps)))
    got_sv_result = cut(got_sv_result, app2,
        apply_thm(and_elim_right(app1, app2, []), [], and_apps, app2, ax(and_apps)))
    imp_sv = Implies(and_apps, eq_b)
    left_sv = [f for f in got_sv_result.sequent.left if not same(f, and_apps)]
    got_sv_result = Proof(Sequent(left_sv, [imp_sv]), 'implies_right',
        [got_sv_result], principal=imp_sv)
    for v in [b2, b1, av]:
        body = got_sv_result.sequent.right[0]
        fa = Forall(v, body)
        got_sv_result = Proof(Sequent(got_sv_result.sequent.left, [fa]),
            'forall_right', [got_sv_result], principal=fa, term=v)

    # Function(t2) = And(Relation(t2), SingleValued(t2))
    func_t2 = FuncDef(t2)
    got_func_t2 = mp(apply_thm(and_intro(rel_t2, got_sv_result.sequent.right[0], []), [],
        rel_t2, Implies(got_sv_result.sequent.right[0], And(rel_t2, got_sv_result.sequent.right[0])),
        got_rel_t2), got_sv_result, got_sv_result.sequent.right[0],
        And(rel_t2, got_sv_result.sequent.right[0]))
    got_func_t2 = cut(ax(func_t2), func_t2, got_func_t2)
    print(f'tape_update_function: Function(t2) done')

    # Cut Relation(t) — derived from Function(t), not a separate hypothesis
    got_func_t2 = cut(got_func_t2, rel_t, got_rel)

    # Discharge hypotheses, close ∀
    proof = got_func_t2
    for hyp in [func_t, tu]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [val, pos, t, t2]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'tape_update_function'
    return proof






def tape_read_high():
    """Read from second group: UnaryTape + In(j,b) + Successor(sa,a) + Plus(sa,j,pos) + Num(one,1)
       -> Apply(tape,pos,one).
    |- forall tape, a, b, j, sa, pos, one.
         UnaryTape(tape,a,b) -> In(j,b) -> Successor(sa,a) -> Plus(sa,j,pos) ->
         Num(one,1) -> Apply(tape,pos,one)"""
    from tactics import apply_thm, mp, ax
    from core.proof import Proof, Sequent, same
    from theorems.logic import and_elim_right
    from tm import UnaryTape
    from vocab.recursion import Plus as PlusDef

    tape, a, b, j, sa, pos, one = Var(), Var(), Var(), Var(), Var(), Var(), Var()
    ut = UnaryTape(tape, a, b)
    in_j_b = In(j, b)
    succ_sa = Successor(sa, a)
    plus_pos = PlusDef(sa, j, pos)
    num_one = Num(one, 1)
    app = Apply(tape, pos, one)

    exp = ut.expand()
    # exp = And(func, And(low, And(sep, And(high, beyond))))
    func_f = exp.left
    rest0 = exp.right  # And(low, And(sep, And(high, beyond)))
    low_f = rest0.left
    rest_f = rest0.right   # And(sep_f, And(high_f, end_f))
    sep_f = rest_f.left
    high_end_f = rest_f.right  # And(high_f, end_f)
    high_f = high_end_f.left
    from theorems.logic import and_elim_left

    # Skip func, extract rest0, then rest, then high_end, then high
    aer0 = and_elim_right(func_f, rest0, [])
    got_rest0 = apply_thm(aer0, [], ut, rest0, ax(ut))
    aer1 = and_elim_right(low_f, rest_f, [])
    got_rest = apply_thm(aer1, [], rest0, rest_f, got_rest0)

    aer2 = and_elim_right(sep_f, high_end_f, [])
    got_high_end = apply_thm(aer2, [], rest_f, high_end_f, got_rest)
    aer3 = and_elim_left(high_f, high_end_f.right, [])
    got_high_only = apply_thm(aer3, [], high_end_f, high_f, got_high_end)
    got_high = got_high_only
    # [ut] |- high_f = Forall(j', In(j',b) -> Forall(sa', Succ(sa',a) -> ...))

    # Instantiate: j, then In(j,b), then sa, then Succ(sa,a), then pos, then Plus, then one, then Num
    got = apply_thm(got_high, [j], in_j_b,
        Forall(sa, Implies(succ_sa, Forall(pos, Implies(plus_pos,
            Forall(one, Implies(num_one, app)))))),
        ax(in_j_b))
    got = apply_thm(got, [sa], succ_sa,
        Forall(pos, Implies(plus_pos, Forall(one, Implies(num_one, app)))),
        ax(succ_sa))
    got = apply_thm(got, [pos], plus_pos,
        Forall(one, Implies(num_one, app)),
        ax(plus_pos))
    got = apply_thm(got, [one], num_one, app, ax(num_one))
    # [ut, In(j,b), Succ(sa,a), Plus(sa,j,pos), Num(one,1)] |- Apply(tape,pos,one)

    # Close
    for premise in [num_one, plus_pos, succ_sa, in_j_b, ut]:
        imp = Implies(premise, got.sequent.right[0])
        left = [f for f in got.sequent.left if not same(f, premise)]
        got = Proof(Sequent(left, [imp]), 'implies_right', [got], principal=imp)

    proof = got
    for v in [one, pos, sa, j, b, a, tape]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'tape_read_high'
    return proof



def tape_update_other():
    """Read at other position: TapeUpdate(tape',tape,h,w) + Apply(tape,x,y) + Not(Eq(x,h))
       -> Apply(tape',x,y).
    Pairing |- forall tape', tape, h, w, x, y.
         TapeUpdate(tape',tape,h,w) -> Apply(tape,x,y) -> Not(Eq(x,h)) -> Apply(tape',x,y)

    Apply(tape,x,y) gives ∃p. OrdPair(p,x,y) ∧ In(p,tape). From Not(Eq(x,h)) and
    OrdPair(p,x,y): ¬∃y'.OrdPair(p,h,y') (via tuple_injection). Then TapeUpdate's
    right disjunct gives In(p,tape') → Apply(tape',x,y)."""
    from tactics import apply_thm, mp, ax, wl, wr, eir, eel, cut
    from core.proof import Proof, Sequent, same
    from theorems.logic import iff_mp_rev, or_intro_right, and_intro
    from theorems.sets import tuple_injection

    tapen, tape, h, w, x, y = Var(), Var(), Var(), Var(), Var(), Var()
    p = Var(postfix='p')
    tu = TapeUpdate(tapen, tape, h, w)
    app_old = Apply(tape, x, y)
    not_eq_xh = Not(Eq(x, h))
    app_new = Apply(tapen, x, y)

    op_pxy = OrdPair(p, x, y)
    in_p_tape = In(p, tape)
    in_p_tapen = In(p, tapen)

    # TapeUpdate Iff components
    yv = Var(postfix='yv')
    not_ex = Not(Exists(yv, OrdPair(p, h, yv)))
    right_and = And(in_p_tape, not_ex)
    or_form = Or(OrdPair(p, h, w), right_and)
    iff_form = Iff(in_p_tapen, or_form)

    # Step 1: Prove ¬∃y'. OrdPair(p, h, y') from OrdPair(p, x, y) + Not(Eq(x, h))
    # Assume ∃y'. OrdPair(p, h, y'). Then ∃y'. OrdPair(p,x,y) ∧ OrdPair(p,h,y').
    # By tuple_injection: Eq(x,h). But Not(Eq(x,h)). Contradiction.
    op_phy = OrdPair(p, h, yv)
    ti = tuple_injection()
    # tuple_injection: Pairing |- ∀a,b,c,d,t. OrdPair(t,a,b) → OrdPair(t,c,d) → And(Eq(a,c),Eq(b,d))
    eq_xh_and_yy = And(Eq(x, h), Eq(y, yv))
    got_ti = apply_thm(ti, [x, y, h, yv, p])
    got_ti = mp(got_ti, ax(op_pxy), op_pxy, Implies(op_phy, eq_xh_and_yy))
    got_ti = mp(got_ti, ax(op_phy), op_phy, eq_xh_and_yy)
    # [Pairing, OrdPair(p,x,y), OrdPair(p,h,yv)] |- And(Eq(x,h), Eq(y,yv))

    # Extract Eq(x,h) from the And
    from theorems.logic import and_elim_left
    ael = and_elim_left(Eq(x, h), Eq(y, yv), [])
    got_eq_xh = apply_thm(ael, [], eq_xh_and_yy, Eq(x, h), got_ti)
    # [Pairing, OrdPair(p,x,y), OrdPair(p,h,yv)] |- Eq(x,h)

    # Contradiction: not_left from [G] |- [Eq(x,h)] gives [G, Not(Eq(x,h))] |- []
    got_bot = Proof(Sequent(list(got_eq_xh.sequent.left) + [not_eq_xh], []),
        'not_left', [got_eq_xh], principal=not_eq_xh)
    # [Pairing, OrdPair(p,x,y), OrdPair(p,h,yv), Not(Eq(x,h))] |- []

    # Close op_phy: implies_right → ¬OrdPair(p,h,yv)
    not_op_phy = Not(op_phy)
    got_not_phy = Proof(Sequent([f for f in got_bot.sequent.left if not same(f, op_phy)],
        [not_op_phy]), 'not_right', [got_bot], principal=not_op_phy)
    # [Pairing, OrdPair(p,x,y), Not(Eq(x,h))] |- ¬OrdPair(p,h,yv)

    # forall_right on yv → ∀yv. ¬OrdPair(p,h,yv)
    fa_not = Forall(yv, not_op_phy)
    got_fa_not = Proof(Sequent(got_not_phy.sequent.left, [fa_not]),
        'forall_right', [got_not_phy], principal=fa_not, term=yv)
    # [Pairing, OrdPair(p,x,y), Not(Eq(x,h))] |- Forall(yv, Not(OrdPair(p,h,yv)))

    # Convert ∀yv.¬P to ¬∃yv.P:
    # ∃yv.P = Not(Forall(yv, Not(P))). So ¬∃yv.P = Not(Not(Forall(yv, Not(P)))).
    # not_left: from [G] |- [Forall(yv,Not(P))] derive [G, Not(Forall(yv,Not(P)))] |- []
    #           i.e., [G, Exists(yv,P)] |- []
    ex_phy = Exists(yv, op_phy)  # = Not(Forall(yv, Not(OrdPair(p,h,yv))))
    got_bot2 = Proof(Sequent(list(got_fa_not.sequent.left) + [ex_phy], []),
        'not_left', [got_fa_not], principal=ex_phy)
    # [Pairing, op_pxy, Not(Eq(x,h)), Exists(yv,OrdPair(p,h,yv))] |- []

    # not_right: [G] |- [Not(Exists(yv, OrdPair(p,h,yv)))]
    got_not_ex = Proof(Sequent([f for f in got_bot2.sequent.left if not same(f, ex_phy)],
        [not_ex]), 'not_right', [got_bot2], principal=not_ex)
    # [Pairing, OrdPair(p,x,y), Not(Eq(x,h))] |- not_ex = ¬∃yv.OrdPair(p,h,yv)

    # Step 2: Build right_and = And(In(p,tape), not_ex)
    ai = and_intro(in_p_tape, not_ex, [])
    got_right = mp(apply_thm(ai, [], in_p_tape,
        Implies(not_ex, right_and), ax(in_p_tape)),
        got_not_ex, not_ex, right_and)
    # [Pairing, OrdPair(p,x,y), Not(Eq(x,h)), In(p,tape)] |- And(In(p,tape), not_ex)

    # Step 3: or_intro_right → Or(OrdPair(p,h,w), right_and)
    from theorems.logic import or_intro_right
    oir = or_intro_right(OrdPair(p, h, w), right_and, [])
    got_or = apply_thm(oir, [], right_and, or_form, got_right)

    # Step 4: TapeUpdate Iff reverse: Or → In(p,tapen)
    got_iff = apply_thm(ax(tu), [p], concl=iff_form)
    iff_rev = iff_mp_rev(in_p_tapen, or_form, [])
    got_imp = apply_thm(iff_rev, [], iff_form,
        Implies(or_form, in_p_tapen), got_iff)
    got_in = mp(got_imp, got_or, or_form, in_p_tapen)
    # [tu, Pairing, OrdPair(p,x,y), Not(Eq(x,h)), In(p,tape)] |- In(p,tapen)

    # Step 5: And(OrdPair(p,x,y), In(p,tapen)) → eir → Apply(tapen,x,y)
    ai2 = and_intro(op_pxy, in_p_tapen, [])
    got_and = mp(apply_thm(ai2, [], op_pxy,
        Implies(in_p_tapen, And(op_pxy, in_p_tapen)), ax(op_pxy)),
        got_in, in_p_tapen, And(op_pxy, in_p_tapen))
    got_apply = eir(got_and, And(op_pxy, in_p_tapen), p, p)

    # Step 6: Eliminate OrdPair(p,x,y) and In(p,tape) from left.
    # These came from Apply(tape,x,y) = ∃p. And(OrdPair(p,x,y), In(p,tape)).
    # eel on In(p,tape): replace with ∃... no, both op_pxy and in_p_tape have p free.
    # We need to eliminate them together. The pair (op_pxy, in_p_tape) comes from
    # Apply(tape,x,y) after eel.
    # Actually, Apply(tape,x,y) = ∃p. And(OrdPair(p,x,y), In(p,tape)).
    # So we need And(op_pxy, in_p_tape) on left, then eel p.

    # First, combine op_pxy and in_p_tape into a single And on the left.
    # got_apply has op_pxy and in_p_tape separately on the left.
    # We can treat them as: [And(op_pxy, in_p_tape), ...] |- app_new
    # via: from [op_pxy, in_p_tape, ...] |- app_new, cut with and_elim's.

    # Actually simpler: eel in_p_tape first (p free in in_p_tape and op_pxy),
    # then eel op_pxy. But eel requires the var (p) not free in the right.
    # p is NOT free in app_new (Apply(tapen,x,y) expands to ∃ with fresh vars). ✓
    # But p IS free in op_pxy (still on left after eel of in_p_tape).
    # So we need to eel BOTH at once... that's the And approach.

    # Better: merge op_pxy and in_p_tape into And, eel p from the And.
    and_form = And(op_pxy, in_p_tape)
    # Need: [and_form, rest] |- app_new  from  [op_pxy, in_p_tape, rest] |- app_new
    # Use and_elim_left/right to extract op_pxy and in_p_tape from and_form.
    from theorems.logic import and_elim_right
    ael_op = and_elim_left(op_pxy, in_p_tape, [])
    aer_in = and_elim_right(op_pxy, in_p_tape, [])
    got_op_from_and = apply_thm(ael_op, [], and_form, op_pxy, ax(and_form))
    got_in_from_and = apply_thm(aer_in, [], and_form, in_p_tape, ax(and_form))
    # [and_form] |- op_pxy, [and_form] |- in_p_tape
    got_apply2 = cut(got_apply, op_pxy, got_op_from_and)
    got_apply2 = cut(got_apply2, in_p_tape, got_in_from_and)
    # [And(op_pxy,in_p_tape), tu, Pairing, Not(Eq(x,h))] |- Apply(tapen,x,y)

    # eel p from And(op_pxy, in_p_tape) → Exists(p, And(op_pxy, in_p_tape)) = Apply(tape,x,y)
    got_apply2 = eel(got_apply2, and_form, p)
    # [∃p.And(op_pxy,in_p_tape), tu, Pairing, Not(Eq(x,h))] |- Apply(tapen,x,y)
    # ∃p.And(op_pxy,in_p_tape) = Apply(tape,x,y)
    # So: [Apply(tape,x,y), tu, Pairing, Not(Eq(x,h))] |- Apply(tapen,x,y)

    # Close
    for premise in [not_eq_xh, app_old, tu]:
        imp = Implies(premise, got_apply2.sequent.right[0])
        left = [f for f in got_apply2.sequent.left if not same(f, premise)]
        got_apply2 = Proof(Sequent(left, [imp]), 'implies_right', [got_apply2], principal=imp)

    proof = got_apply2
    for v in [y, x, w, h, tape, tapen]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'tape_update_other'
    return proof



def tape_update_at():
    """Read at written position: TapeUpdate(tape',tape,h,w) + Eq(x,h) + Eq(y,w) -> Apply(tape',x,y).
    Pairing |- forall tape', tape, h, w, x, y.
         TapeUpdate(tape',tape,h,w) -> Eq(x,h) -> Eq(y,w) -> Apply(tape',x,y)

    New TapeUpdate uses In/OrdPair. Apply(tape',x,y) = ∃p. OrdPair(p,x,y) ∧ In(p,tape').
    Get OrdPair(p,x,y) from ordpair_exists. Transfer to OrdPair(p,h,w) via Eq's.
    In(p,tape') from TapeUpdate Iff reverse + left disjunct OrdPair(p,h,w)."""
    from tactics import apply_thm, mp, ax, fl, wl, eir, eel, cut
    from core.proof import Proof, Sequent, same
    from theorems.logic import iff_mp_rev, or_intro_left, and_intro
    from theorems.sets import ordpair_exists, ordpair_eq_transfer

    tapen, tape, h, w, x, y = Var(), Var(), Var(), Var(), Var(), Var()
    p = Var(postfix='p')
    tu = TapeUpdate(tapen, tape, h, w)
    eq_xh = Eq(x, h)
    eq_yw = Eq(y, w)
    app_new = Apply(tapen, x, y)

    # TapeUpdate = ∀p. Iff(In(p, tapen), Or(OrdPair(p,h,w), And(In(p,tape), ¬∃y.OrdPair(p,h,y))))
    yv = Var(postfix='yv')
    right_and = And(In(p, tape), Not(Exists(yv, OrdPair(p, h, yv))))
    or_form = Or(OrdPair(p, h, w), right_and)
    iff_form = Iff(In(p, tapen), or_form)

    # Step 1: ordpair_exists → ∃p. OrdPair(p, x, y)
    oe = ordpair_exists()
    op_pxy = OrdPair(p, x, y)
    got_ex_p = apply_thm(oe, [x, y], concl=Exists(p, op_pxy))
    # [Pairing] |- ∃p. OrdPair(p, x, y)

    # Step 2: Transfer OrdPair(p, x, y) to OrdPair(p, h, w) via Eq(x,h), Eq(y,w)
    # ordpair_eq_transfer: Eq(a,c) → Eq(b,d) → OrdPair(t,a,b) → OrdPair(t,c,d)
    oet = ordpair_eq_transfer()
    op_phw = OrdPair(p, h, w)
    got_ophw = apply_thm(oet, [x, y, h, w, p])
    got_ophw = mp(got_ophw, ax(eq_xh), eq_xh, got_ophw.sequent.right[0].right)
    got_ophw = mp(got_ophw, ax(eq_yw), eq_yw, got_ophw.sequent.right[0].right)
    got_ophw = mp(got_ophw, ax(op_pxy), op_pxy, op_phw)
    # [Eq(x,h), Eq(y,w), OrdPair(p,x,y)] |- OrdPair(p, h, w)

    # Step 3: From TapeUpdate, instantiate with p: Iff(In(p,tapen), Or(...))
    got_iff = apply_thm(ax(tu), [p], concl=iff_form)
    # [tu] |- Iff(In(p,tapen), Or(OrdPair(p,h,w), ...))

    # Iff reverse: Or → In(p,tapen)
    iff_rev = iff_mp_rev(In(p, tapen), or_form, [])
    got_imp = apply_thm(iff_rev, [], iff_form,
        Implies(or_form, In(p, tapen)), got_iff)
    # [tu] |- Or(...) → In(p, tapen)

    # or_intro_left: OrdPair(p,h,w) → Or(OrdPair(p,h,w), ...)
    oil = or_intro_left(op_phw, right_and, [])
    got_or = apply_thm(oil, [], op_phw, or_form, got_ophw)
    # [Eq(x,h), Eq(y,w), OrdPair(p,x,y)] |- Or(...)

    # mp: In(p, tapen)
    got_in = mp(got_imp, got_or, or_form, In(p, tapen))
    # [tu, Eq(x,h), Eq(y,w), OrdPair(p,x,y)] |- In(p, tapen)

    # Step 4: Build Apply(tapen, x, y) = ∃p. And(OrdPair(p,x,y), In(p,tapen))
    # and_intro: OrdPair(p,x,y) ∧ In(p,tapen)
    ai = and_intro(op_pxy, In(p, tapen), [])
    got_and = mp(apply_thm(ai, [], op_pxy,
        Implies(In(p, tapen), And(op_pxy, In(p, tapen))), ax(op_pxy)),
        got_in, In(p, tapen), And(op_pxy, In(p, tapen)))
    # [..., OrdPair(p,x,y)] |- And(OrdPair(p,x,y), In(p,tapen))

    # eir p → ∃p. And(OrdPair(p,x,y), In(p,tapen)) = Apply(tapen,x,y)
    got_apply = eir(got_and, And(op_pxy, In(p, tapen)), p, p)
    # [..., OrdPair(p,x,y)] |- Apply(tapen, x, y)

    # Eliminate OrdPair(p,x,y) from left via eel + cut with got_ex_p
    got_apply = eel(got_apply, op_pxy, p)
    got_apply = cut(got_apply, Exists(p, op_pxy), got_ex_p)
    # [Pairing, tu, Eq(x,h), Eq(y,w)] |- Apply(tapen, x, y)

    # Close
    for premise in [eq_yw, eq_xh, tu]:
        imp = Implies(premise, got_apply.sequent.right[0])
        left = [f for f in got_apply.sequent.left if not same(f, premise)]
        got_apply = Proof(Sequent(left, [imp]), 'implies_right', [got_apply], principal=imp)

    proof = got_apply
    for v in [y, x, w, h, tape, tapen]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'tape_update_at'
    return proof


def tape_update_other_rev():
    """Reverse read at other position: TapeUpdate(tape',tape,h,w) + Apply(tape',x,y) + Not(Eq(x,h))
       -> Apply(tape,x,y).
    Pairing |- forall tape', tape, h, w, x, y.
         TapeUpdate(tape',tape,h,w) -> Apply(tape',x,y) -> Not(Eq(x,h)) -> Apply(tape,x,y)

    Apply(tape',x,y) = ∃p. And(OrdPair(p,x,y), In(p,tape')).
    Open ∃: assume And(OrdPair(p,x,y), In(p,tape')). From In(p,tape') + TapeUpdate Iff fwd:
    Or(OrdPair(p,h,w), And(In(p,tape), ¬∃y'.OrdPair(p,h,y'))).
    Case OrdPair(p,h,w): tuple_injection → Eq(x,h). But Not(Eq(x,h)). Contradiction.
    Case In(p,tape): And(OrdPair(p,x,y), In(p,tape)) → Apply(tape,x,y).
    Close ∃p, cut with Apply(tape',x,y)."""
    from tactics import apply_thm, mp, ax, wl, wr, eir, eel, cut
    from core.proof import Proof, Sequent, same
    from theorems.logic import (iff_mp, or_elim, and_elim_left, and_elim_right, and_intro)
    from theorems.sets import tuple_injection

    tapen, tape, h, w_v, x, y = Var(), Var(), Var(), Var(), Var(), Var()
    p = Var(postfix='p')
    tu = TapeUpdate(tapen, tape, h, w_v)
    app_new = Apply(tapen, x, y)
    not_eq_xh = Not(Eq(x, h))
    app_old = Apply(tape, x, y)

    op_pxy = OrdPair(p, x, y)
    in_p_tape = In(p, tape)
    in_p_tapen = In(p, tapen)

    yv = Var(postfix='yv')
    not_ex = Not(Exists(yv, OrdPair(p, h, yv)))
    right_and = And(in_p_tape, not_ex)
    op_phw = OrdPair(p, h, w_v)
    or_form = Or(op_phw, right_and)
    iff_form = Iff(in_p_tapen, or_form)

    # TapeUpdate Iff forward: In(p,tape') → Or(...)
    got_iff = apply_thm(ax(tu), [p], concl=iff_form)
    got_fwd = apply_thm(iff_mp(in_p_tapen, or_form, []), [],
        iff_form, Implies(in_p_tapen, or_form), got_iff)

    # Open Apply(tape',x,y) = ∃p. And(OrdPair(p,x,y), In(p,tape'))
    # Start from and_apply = And(OrdPair(p,x,y), In(p,tapen))
    and_apply = And(op_pxy, in_p_tapen)
    got_opxy = apply_thm(and_elim_left(op_pxy, in_p_tapen, []), [],
        and_apply, op_pxy, ax(and_apply))
    got_in_ptn = apply_thm(and_elim_right(op_pxy, in_p_tapen, []), [],
        and_apply, in_p_tapen, ax(and_apply))

    # In(p,tape') + TapeUpdate → Or
    got_or = mp(got_fwd, got_in_ptn, in_p_tapen, or_form)

    # Case 1: OrdPair(p,h,w) → contradiction
    ti = tuple_injection()
    eq_xh_and = And(Eq(x, h), Eq(y, w_v))
    got_ti = apply_thm(ti, [x, y, h, w_v, p])
    got_ti = mp(got_ti, got_opxy, op_pxy, got_ti.sequent.right[0].right)
    got_ti = mp(got_ti, ax(op_phw), op_phw, eq_xh_and)
    got_eq_xh = apply_thm(and_elim_left(Eq(x,h), Eq(y,w_v), []), [],
        eq_xh_and, Eq(x,h), got_ti)
    got_bot = Proof(Sequent([Eq(x,h), not_eq_xh], []), 'not_left', [ax(Eq(x,h))], principal=not_eq_xh)
    got_bot = Proof(Sequent(got_bot.sequent.left, [app_old]), 'weakening_right', [got_bot], principal=app_old)
    got_bot = cut(got_bot, Eq(x,h), got_eq_xh)

    # Case 2: And(In(p,tape), ¬∃y'...) → Apply(tape,x,y)
    got_in_pt = apply_thm(and_elim_left(in_p_tape, not_ex, []), [],
        right_and, in_p_tape, ax(right_and))
    and_app_old = And(op_pxy, in_p_tape)
    got_and_old = mp(apply_thm(and_intro(op_pxy, in_p_tape, []), [],
        op_pxy, Implies(in_p_tape, and_app_old), got_opxy),
        got_in_pt, in_p_tape, and_app_old)
    got_app_old = eir(got_and_old, and_app_old, p, p)

    # or_elim on Or(OrdPair(p,h,w), And(In(p,tape), ¬∃...))
    imp_c1 = Implies(op_phw, app_old)
    left_c1 = [f for f in got_bot.sequent.left if not same(f, op_phw)]
    got_imp_c1 = Proof(Sequent(left_c1, [imp_c1]), 'implies_right', [got_bot], principal=imp_c1)
    imp_c2 = Implies(right_and, app_old)
    left_c2 = [f for f in got_app_old.sequent.left if not same(f, right_and)]
    got_imp_c2 = Proof(Sequent(left_c2, [imp_c2]), 'implies_right', [got_app_old], principal=imp_c2)
    oe = or_elim(op_phw, right_and, app_old, [])
    got_result = apply_thm(oe, [], or_form,
        Implies(imp_c1, Implies(imp_c2, app_old)), ax(or_form))
    got_result = mp(got_result, got_imp_c1, imp_c1, Implies(imp_c2, app_old))
    got_result = mp(got_result, got_imp_c2, imp_c2, app_old)
    got_result = cut(got_result, or_form, got_or)
    # [and_apply, tu, ¬Eq(x,h), Pairing] |- Apply(tape,x,y)

    # eel p from and_apply, cut with Apply(tape',x,y)
    got_result = eel(got_result, and_apply, p)
    got_result = cut(got_result, Exists(p, and_apply), ax(app_new))

    # Close
    for premise in [not_eq_xh, app_new, tu]:
        got_result = wl(got_result, premise)
        imp = Implies(premise, got_result.sequent.right[0])
        left = [f for f in got_result.sequent.left if not same(f, premise)]
        got_result = Proof(Sequent(left, [imp]), 'implies_right', [got_result], principal=imp)

    proof = got_result
    for v in [y, x, w_v, h, tape, tapen]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'tape_update_other_rev'
    return proof


def config_exists():
    """∃c. TMConfig(c, q, h, t) — a config with given state/head/tape exists.
    Pairing |- ∀q,h,t. ∃c. TMConfig(c,q,h,t)"""
    from tactics import apply_thm, mp, ax, eir, eel, cut
    from theorems.sets import ordpair_exists
    from core.proof import Proof, Sequent, same

    q, h, t = Var(postfix='_q'), Var(postfix='_h'), Var(postfix='_t')
    c = Var(postfix='_c')
    inner = Var(postfix='_inn')

    # config_intro: ∀c,q,h,t,inner. OrdPair(inner,h,t) → OrdPair(c,q,inner) → TMConfig(c,q,h,t)
    ci = config_intro()
    got = apply_thm(ci, [c, q, h, t, inner])
    # got: [Pairing] |- OrdPair(inner,h,t) → OrdPair(c,q,inner) → TMConfig(c,q,h,t)

    op_inner = OrdPair(inner, h, t)
    op_c = OrdPair(c, q, inner)
    cfg = TMConfig(c, q, h, t)

    # ordpair_exists: ∀a,b. ∃p. OrdPair(p,a,b)
    oe = ordpair_exists()
    got_ex_inner = apply_thm(oe, [h, t], concl=Exists(inner, op_inner))
    got_ex_c = apply_thm(oe, [q, inner], concl=Exists(c, op_c))

    # mp: provide OrdPair(inner,h,t) and OrdPair(c,q,inner) → TMConfig(c,q,h,t)
    got = mp(got, ax(op_inner), op_inner, Implies(op_c, cfg))
    got = mp(got, ax(op_c), op_c, cfg)
    # [op_inner, op_c, Pairing] |- TMConfig(c,q,h,t)

    # eir c → ∃c. TMConfig(c,q,h,t)
    got = eir(got, cfg, c, c)
    # eel c from op_c, cut with got_ex_c
    got = eel(got, op_c, c)
    got = cut(got, Exists(c, op_c), got_ex_c)
    # eel inner from op_inner, cut with got_ex_inner
    got = eel(got, op_inner, inner)
    got = cut(got, Exists(inner, op_inner), got_ex_inner)
    # [Pairing] |- ∃c. TMConfig(c,q,h,t)

    proof = got
    for v in [t, h, q]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'config_exists'
    return proof


# ============================================================
# derive_tu_tf: derive TapeUpdate(tf,tape2,c,z) from UnaryOutput + func_ext
# ============================================================

def derive_tu_tf(tf, tape2, tape_in, c, z, a, b, w, sa, one, hf,
                 utape, tu_tape2, unary_out, succ_sa, succ_hf,
                 plus_abc, num_one, num_z, omega_w,
                 got_sa_w, got_hf_w, got_psbh, got_c_w):
    """Derive TapeUpdate(tf, tape2, c, z) from UnaryOutput(tf,c) + tape semantics via func_ext.

    Returns proof of TapeUpdate(tf,tape2,c,z) with goal hyps + ZFC on left.
    """
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from core.proof import Proof, Sequent, same
    from core.lang import Var, In, Implies, Forall, Not
    from core.derived import Exists, And, Or, Iff, Eq
    from vocab.ordpair import Successor
    from vocab.omega import Num
    from vocab.tm import TapeUpdate
    from vocab.functions import Function as FuncDef, Apply
    from vocab.recursion import Plus as PlusDef
    from tm import UnaryTape, UnaryOutput
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        or_intro_left, or_intro_right, or_elim, eq_reflexive, eq_symmetric,
        eq_transitive, iff_mp, iff_mp_rev, iff_intro, eq_substitution)
    from theorems.sets import (omega_no_self_membership, eq_transfer as eq_transfer_fn,
        omega_transitive, func_ext)
    from theorems.omega import func_unique_thm
    from theorems.recursion import eq_apply_transfer, eq_apply_val_transfer
    from theorems.arithmetic import plus_bounded_exists, plus_geq, plus_val_unique

    tu_tf_formula = TapeUpdate(tf, tape2, c, z)
    _tua = tape_update_at()
    _tuo = tape_update_other()
    _tuor = tape_update_other_rev()
    _trh = tape_read_high()
    _fut = func_unique_thm()
    _onsm = omega_no_self_membership()
    _et = eq_transfer_fn()
    _esub = eq_substitution()
    _es = eq_symmetric()
    _eavt = eq_apply_val_transfer()
    _eat = eq_apply_transfer()

    # --- Step 1: ∃t2'. TapeUpdate(t2', tape2, c, z) ---
    _tue = tape_update_exists()
    got_tue = apply_thm(_tue, [tape2, c, z])
    t2p = got_tue.sequent.right[0].var
    t2p_body = got_tue.sequent.right[0].body
    print(f'tu_tf: step 1 tape_update_exists OK')

    # --- Step 2: Function(t2') ---
    _tuf = tape_update_function()
    got_func_t2p = apply_thm(_tuf, [t2p, tape2, c, z])
    got_func_t2p = mp(got_func_t2p, ax(t2p_body), t2p_body, got_func_t2p.sequent.right[0].right)
    got_func_t2_inner = apply_thm(tape_update_function(), [tape2, tape_in, a, one])
    got_func_t2_inner = mp(got_func_t2_inner, ax(tu_tape2), tu_tape2, got_func_t2_inner.sequent.right[0].right)
    got_func_t2_inner = mp(got_func_t2_inner, ax(FuncDef(tape_in)), FuncDef(tape_in), FuncDef(tape2))
    got_func_t2p = mp(got_func_t2p, got_func_t2_inner, FuncDef(tape2), FuncDef(t2p))

    # --- Step 3: Function(tf) + UO ones/zeros ---
    uo_exp = unary_out.expand()
    got_func_tf = apply_thm(and_elim_left(uo_exp.left, uo_exp.right, []), [],
        unary_out, uo_exp.left, ax(unary_out))
    got_uo_rest = apply_thm(and_elim_right(uo_exp.left, uo_exp.right, []), [],
        unary_out, uo_exp.right, ax(unary_out))
    ones_f = uo_exp.right.left
    zeros_f = uo_exp.right.right
    got_ones = apply_thm(and_elim_left(ones_f, zeros_f, []), [],
        uo_exp.right, ones_f, got_uo_rest)
    got_zeros = apply_thm(and_elim_right(ones_f, zeros_f, []), [],
        uo_exp.right, zeros_f, got_uo_rest)

    # Extract UnaryTape components
    ut_exp = utape.expand()
    got_ut_rest = apply_thm(and_elim_right(ut_exp.left, ut_exp.right, []), [],
        utape, ut_exp.right, ax(utape))
    low_f = ut_exp.right.left
    got_ut_low = apply_thm(and_elim_left(low_f, ut_exp.right.right, []), [],
        ut_exp.right, low_f, got_ut_rest)
    # beyond
    got_ut_rest2 = apply_thm(and_elim_right(ut_exp.left, ut_exp.right, []), [],
        utape, ut_exp.right, ax(utape))
    r1 = ut_exp.right.right
    got_r1 = apply_thm(and_elim_right(ut_exp.right.left, r1, []), [],
        ut_exp.right, r1, got_ut_rest2)
    r2 = r1.right
    got_r2 = apply_thm(and_elim_right(r1.left, r2, []), [], r1, r2, got_r1)
    beyond_f = r2.right
    got_beyond = apply_thm(and_elim_right(r2.left, beyond_f, []), [], r2, beyond_f, got_r2)
    print(f'tu_tf: step 3 UO + UT decomposed')

    # Helper: derive Or(Eq(a,c),In(a,c)) from plus_geq + plus_val_unique
    def derive_or_ac():
        _pg = plus_geq()
        got_pg = apply_thm(_pg, [w, a, b])
        got_pg = mp(got_pg, ax(omega_w), omega_w, got_pg.sequent.right[0].right)
        got_pg = mp(got_pg, ax(In(a,w)), In(a,w), got_pg.sequent.right[0].right)
        got_pg = mp(got_pg, ax(In(b,w)), In(b,w), got_pg.sequent.right[0].right)
        pg_cv = got_pg.sequent.right[0].var
        pg_bd = got_pg.sequent.right[0].body
        got_plus_cv = apply_thm(and_elim_left(pg_bd.left, pg_bd.right, []), [],
            pg_bd, pg_bd.left, ax(pg_bd))
        got_or_cv = apply_thm(and_elim_right(pg_bd.left, pg_bd.right, []), [],
            pg_bd, pg_bd.right, ax(pg_bd))
        _pvu = plus_val_unique()
        got_eq_c_cv = apply_thm(_pvu, [w, a, b, c, pg_cv])
        got_eq_c_cv = mp(got_eq_c_cv, ax(omega_w), omega_w, got_eq_c_cv.sequent.right[0].right)
        got_eq_c_cv = mp(got_eq_c_cv, ax(In(a,w)), In(a,w), got_eq_c_cv.sequent.right[0].right)
        got_eq_c_cv = mp(got_eq_c_cv, ax(In(b,w)), In(b,w), got_eq_c_cv.sequent.right[0].right)
        got_eq_c_cv = mp(got_eq_c_cv, ax(plus_abc), plus_abc, got_eq_c_cv.sequent.right[0].right)
        got_eq_c_cv = mp(got_eq_c_cv, got_plus_cv, pg_bd.left, Eq(c, pg_cv))
        got_eq_cv_c = apply_thm(_es, [c, pg_cv], Eq(c, pg_cv), Eq(pg_cv, c), got_eq_c_cv)
        _et2 = eq_transfer_fn()
        got_iff_ac = apply_thm(_et2, [pg_cv, c, a])
        got_iff_ac = mp(got_iff_ac, got_eq_cv_c, Eq(pg_cv,c), got_iff_ac.sequent.right[0].right)
        _etr = eq_transitive()
        or_ac = Or(Eq(a,c), In(a,c))
        got_eq_a_c = apply_thm(_etr, [a, pg_cv, c])
        got_eq_a_c = mp(got_eq_a_c, ax(Eq(a,pg_cv)), Eq(a,pg_cv), got_eq_a_c.sequent.right[0].right)
        got_eq_a_c = mp(got_eq_a_c, got_eq_cv_c, Eq(pg_cv,c), Eq(a,c))
        got_or_eq = apply_thm(or_intro_left(Eq(a,c), In(a,c), []), [], Eq(a,c), or_ac, got_eq_a_c)
        got_in_a_c = mp(apply_thm(iff_mp(In(a,pg_cv), In(a,c), []), [],
            Iff(In(a,pg_cv), In(a,c)), Implies(In(a,pg_cv), In(a,c)), got_iff_ac),
            ax(In(a,pg_cv)), In(a,pg_cv), In(a,c))
        got_or_in = apply_thm(or_intro_right(Eq(a,c), In(a,c), []), [], In(a,c), or_ac, got_in_a_c)
        or_cv = Or(Eq(a,pg_cv), In(a,pg_cv))
        oe = or_elim(Eq(a,pg_cv), In(a,pg_cv), or_ac, [])
        imp_eq_or = Implies(Eq(a,pg_cv), or_ac)
        got_imp_eq = Proof(Sequent([f for f in got_or_eq.sequent.left if not same(f, Eq(a,pg_cv))],
            [imp_eq_or]), 'implies_right', [got_or_eq], principal=imp_eq_or)
        imp_in_or = Implies(In(a,pg_cv), or_ac)
        got_imp_in = Proof(Sequent([f for f in got_or_in.sequent.left if not same(f, In(a,pg_cv))],
            [imp_in_or]), 'implies_right', [got_or_in], principal=imp_in_or)
        got_or_final = apply_thm(oe, [], or_cv,
            Implies(imp_eq_or, Implies(imp_in_or, or_ac)), ax(or_cv))
        got_or_final = mp(got_or_final, got_imp_eq, imp_eq_or, Implies(imp_in_or, or_ac))
        got_or_final = mp(got_or_final, got_imp_in, imp_in_or, or_ac)
        got_or_final = cut(got_or_final, or_cv, got_or_cv)
        got_or_final = eel(got_or_final, pg_bd, pg_cv)
        got_or_final = cut(got_or_final, got_pg.sequent.right[0], got_pg)
        return got_or_final

    got_or_ac = derive_or_ac()
    or_ac = Or(Eq(a,c), In(a,c))
    # Derive In(a,hf) from Or(Eq(a,c),In(a,c)) + Successor(hf,c)
    or_a_c_2 = Or(In(a,c), Eq(a,c))
    got_or_rearr2 = apply_thm(or_intro_right(In(a,c), Eq(a,c), []), [], Eq(a,c), or_a_c_2, ax(Eq(a,c)))
    got_or_rearr3 = apply_thm(or_intro_left(In(a,c), Eq(a,c), []), [], In(a,c), or_a_c_2, ax(In(a,c)))
    oe_rearr = or_elim(Eq(a,c), In(a,c), or_a_c_2, [])
    imp_eq_or_r = Implies(Eq(a,c), or_a_c_2)
    got_imp_eq_r = Proof(Sequent([], [imp_eq_or_r]), 'implies_right', [got_or_rearr2], principal=imp_eq_or_r)
    imp_in_or_r = Implies(In(a,c), or_a_c_2)
    got_imp_in_r = Proof(Sequent([], [imp_in_or_r]), 'implies_right', [got_or_rearr3], principal=imp_in_or_r)
    got_or_ac_rearr = apply_thm(oe_rearr, [], or_ac,
        Implies(imp_eq_or_r, Implies(imp_in_or_r, or_a_c_2)), ax(or_ac))
    got_or_ac_rearr = mp(got_or_ac_rearr, got_imp_eq_r, imp_eq_or_r, Implies(imp_in_or_r, or_a_c_2))
    got_or_ac_rearr = mp(got_or_ac_rearr, got_imp_in_r, imp_in_or_r, or_a_c_2)
    got_or_ac_rearr = cut(got_or_ac_rearr, or_ac, got_or_ac)
    got_iff_ahf = fl(succ_hf, Iff(In(a,hf), or_a_c_2), a)
    got_in_a_hf = mp(apply_thm(iff_mp_rev(In(a,hf), or_a_c_2, []), [],
        got_iff_ahf.sequent.right[0], Implies(or_a_c_2, In(a,hf)), got_iff_ahf),
        got_or_ac_rearr, or_a_c_2, In(a,hf))

    got_eq_oo = apply_thm(eq_reflexive(), [one])

    # Helper: LEM pattern for ¬P from (P → ¬P)
    def lem_not(got_imp_p_notp, p_formula, notp_formula):
        rest = [f for f in got_imp_p_notp.sequent.left if not same(f, p_formula)]
        imp = Implies(p_formula, notp_formula)
        got_imp = Proof(Sequent(rest, [imp]), 'implies_right', [got_imp_p_notp], principal=imp)
        got_lem = Proof(Sequent([], [notp_formula, p_formula]), 'not_right', [ax(p_formula)], principal=notp_formula)
        got_use = Proof(Sequent([imp], [notp_formula]), 'implies_left', [got_lem, ax(notp_formula)], principal=imp)
        return cut(got_use, imp, got_imp)

    # Helper: derive ¬Eq(xv,c) from In(xv,c) via omega no self membership
    def derive_not_eq_xvc(xv):
        not_eq = Not(Eq(xv,c))
        got_xv_w = apply_thm(omega_transitive(), [w, c, xv])
        got_xv_w = mp(got_xv_w, ax(omega_w), omega_w, got_xv_w.sequent.right[0].right)
        got_xv_w = mp(got_xv_w, got_c_w, In(c,w), got_xv_w.sequent.right[0].right)
        got_xv_w = mp(got_xv_w, ax(In(xv,c)), In(xv,c), In(xv,w))
        got_not_xx = apply_thm(_onsm, [w, xv])
        got_not_xx = mp(got_not_xx, ax(omega_w), omega_w, got_not_xx.sequent.right[0].right)
        got_not_xx = mp(got_not_xx, got_xv_w, In(xv,w), Not(In(xv,xv)))
        got_iff = apply_thm(_et, [c, xv, xv])
        got_iff = mp(got_iff, ax(Eq(c,xv)), Eq(c,xv), got_iff.sequent.right[0].right)
        got_in_xx = mp(apply_thm(iff_mp(In(xv,c), In(xv,xv), []), [],
            Iff(In(xv,c), In(xv,xv)), Implies(In(xv,c), In(xv,xv)), got_iff),
            ax(In(xv,c)), In(xv,c), In(xv,xv))
        got_bot = Proof(Sequent([In(xv,xv), Not(In(xv,xv))], []), 'not_left', [ax(In(xv,xv))], principal=Not(In(xv,xv)))
        got_bot = Proof(Sequent(got_bot.sequent.left, [not_eq]), 'weakening_right', [got_bot], principal=not_eq)
        got_bot = cut(got_bot, Not(In(xv,xv)), got_not_xx)
        got_bot = cut(got_bot, In(xv,xv), got_in_xx)
        got_eq_cxv = apply_thm(_es, [xv, c], Eq(xv,c), Eq(c,xv), ax(Eq(xv,c)))
        got_bot = cut(got_bot, Eq(c,xv), got_eq_cxv)
        return lem_not(got_bot, Eq(xv,c), not_eq)

    # Helper: derive ¬In(xv,hf) from ¬In(xv,c) ∧ ¬Eq(xv,c) via Successor(hf,c)
    def derive_not_in_xvhf(xv):
        not_in_xvc = Not(In(xv,c)); not_eq_xvc = Not(Eq(xv,c)); not_in_xvhf = Not(In(xv,hf))
        got_iff = fl(succ_hf, Iff(In(xv,hf), Or(In(xv,c), Eq(xv,c))), xv)
        got_mp_fwd = apply_thm(iff_mp(In(xv,hf), Or(In(xv,c), Eq(xv,c)), []), [],
            got_iff.sequent.right[0], Implies(In(xv,hf), Or(In(xv,c), Eq(xv,c))), got_iff)
        got_or = mp(got_mp_fwd, ax(In(xv,hf)), In(xv,hf), Or(In(xv,c), Eq(xv,c)))
        or_ie = Or(In(xv,c), Eq(xv,c))
        bot_in = Proof(Sequent([In(xv,c), not_in_xvc], []), 'not_left', [ax(In(xv,c))], principal=not_in_xvc)
        bot_in = Proof(Sequent(bot_in.sequent.left, [not_in_xvhf]), 'weakening_right', [bot_in], principal=not_in_xvhf)
        bot_eq = Proof(Sequent([Eq(xv,c), not_eq_xvc], []), 'not_left', [ax(Eq(xv,c))], principal=not_eq_xvc)
        bot_eq = Proof(Sequent(bot_eq.sequent.left, [not_in_xvhf]), 'weakening_right', [bot_eq], principal=not_in_xvhf)
        oe = or_elim(In(xv,c), Eq(xv,c), not_in_xvhf, [])
        imp_in = Implies(In(xv,c), not_in_xvhf)
        got_imp_in = Proof(Sequent([not_in_xvc], [imp_in]), 'implies_right', [bot_in], principal=imp_in)
        imp_eq = Implies(Eq(xv,c), not_in_xvhf)
        got_imp_eq = Proof(Sequent([not_eq_xvc], [imp_eq]), 'implies_right', [bot_eq], principal=imp_eq)
        got_oe = apply_thm(oe, [], or_ie, Implies(imp_in, Implies(imp_eq, not_in_xvhf)), ax(or_ie))
        got_oe = mp(got_oe, got_imp_in, imp_in, Implies(imp_eq, not_in_xvhf))
        got_oe = mp(got_oe, got_imp_eq, imp_eq, not_in_xvhf)
        got_oe = cut(got_oe, or_ie, got_or)
        rest = [f for f in got_oe.sequent.left if not same(f, In(xv,hf))]
        imp_inhf = Implies(In(xv,hf), not_in_xvhf)
        got_imp_inhf = Proof(Sequent(rest, [imp_inhf]), 'implies_right', [got_oe], principal=imp_inhf)
        got_lem = Proof(Sequent([], [not_in_xvhf, In(xv,hf)]), 'not_right', [ax(In(xv,hf))], principal=not_in_xvhf)
        got_use = Proof(Sequent([imp_inhf], [not_in_xvhf]), 'implies_left', [got_lem, ax(not_in_xvhf)], principal=imp_inhf)
        return cut(got_use, imp_inhf, got_imp_inhf)

    # Helper: derive ¬Eq(xv,a) from ¬In(xv,hf) + In(a,hf)
    def derive_not_eq_xva(xv, got_not_in_xvhf):
        not_eq_xva = Not(Eq(xv,a))
        got_iff = apply_thm(_esub, [xv, a, hf])
        got_iff = mp(got_iff, ax(Eq(xv,a)), Eq(xv,a), got_iff.sequent.right[0].right)
        got_in_xvhf = mp(apply_thm(iff_mp_rev(In(xv,hf), In(a,hf), []), [],
            Iff(In(xv,hf), In(a,hf)), Implies(In(a,hf), In(xv,hf)), got_iff),
            got_in_a_hf, In(a,hf), In(xv,hf))
        not_in_xvhf = Not(In(xv,hf))
        bot = Proof(Sequent([In(xv,hf), not_in_xvhf], []), 'not_left', [ax(In(xv,hf))], principal=not_in_xvhf)
        bot = Proof(Sequent(bot.sequent.left, [not_eq_xva]), 'weakening_right', [bot], principal=not_eq_xva)
        bot = cut(bot, In(xv,hf), got_in_xvhf)
        bot = cut(bot, not_in_xvhf, got_not_in_xvhf)
        return lem_not(bot, Eq(xv,a), not_eq_xva)

    # Helper: Apply(tape2,xv,one) for In(xv,c) via 3-case LEM
    def derive_tape2_xv_one(xv):
        app_t2_xv_one = Apply(tape2, xv, one)
        # Case Eq(xv,a): tape_update_at
        c1 = apply_thm(_tua, [tape2, tape_in, a, one, xv, one])
        c1 = mp(c1, ax(tu_tape2), tu_tape2, c1.sequent.right[0].right)
        c1 = mp(c1, ax(Eq(xv,a)), Eq(xv,a), c1.sequent.right[0].right)
        c1 = mp(c1, got_eq_oo, Eq(one,one), c1.sequent.right[0].right)
        c1 = cut(ax(app_t2_xv_one), app_t2_xv_one, c1)
        # Case In(xv,a): tape_read_low + tape_update_other
        got_tin_low = apply_thm(got_ut_low, [xv])
        got_tin_low = mp(got_tin_low, ax(In(xv,a)), In(xv,a), got_tin_low.sequent.right[0].right)
        got_tin_low = apply_thm(got_tin_low, [one])
        got_tin_low = mp(got_tin_low, ax(num_one), num_one, Apply(tape_in,xv,one))
        c2_low = apply_thm(_tuo, [tape2, tape_in, a, one, xv, one])
        c2_low = mp(c2_low, ax(tu_tape2), tu_tape2, c2_low.sequent.right[0].right)
        c2_low = mp(c2_low, got_tin_low, Apply(tape_in,xv,one), c2_low.sequent.right[0].right)
        c2_low = mp(c2_low, ax(Not(Eq(xv,a))), Not(Eq(xv,a)), c2_low.sequent.right[0].right)
        c2_low = cut(ax(app_t2_xv_one), app_t2_xv_one, c2_low)
        # Case ¬In(xv,a) ∧ ¬Eq(xv,a): plus_bounded_exists + tape_read_high + tape_update_other
        _pbe = plus_bounded_exists()
        got_pbe = apply_thm(_pbe, [w, a, sa, b])
        got_pbe = mp(got_pbe, ax(omega_w), omega_w, got_pbe.sequent.right[0].right)
        got_pbe = mp(got_pbe, ax(In(a,w)), In(a,w), got_pbe.sequent.right[0].right)
        got_pbe = mp(got_pbe, ax(In(b,w)), In(b,w), got_pbe.sequent.right[0].right)
        got_pbe = mp(got_pbe, ax(succ_sa), succ_sa, got_pbe.sequent.right[0].right)
        got_pbe = apply_thm(got_pbe, [c])
        got_pbe = mp(got_pbe, ax(plus_abc), plus_abc, got_pbe.sequent.right[0].right)
        got_pbe = apply_thm(got_pbe, [xv])
        got_pbe = mp(got_pbe, ax(In(xv,c)), In(xv,c), got_pbe.sequent.right[0].right)
        got_pbe = mp(got_pbe, ax(Not(In(xv,a))), Not(In(xv,a)), got_pbe.sequent.right[0].right)
        got_pbe = mp(got_pbe, ax(Not(Eq(xv,a))), Not(Eq(xv,a)), got_pbe.sequent.right[0].right)
        jv = got_pbe.sequent.right[0].var
        jv_body = got_pbe.sequent.right[0].body
        got_in_jv = apply_thm(and_elim_left(jv_body.left, jv_body.right, []), [],
            jv_body, jv_body.left, ax(jv_body))
        got_plus_jv = apply_thm(and_elim_right(jv_body.left, jv_body.right, []), [],
            jv_body, jv_body.right, ax(jv_body))
        got_tin_high = apply_thm(_trh, [tape_in, a, b, jv, sa, xv, one])
        got_tin_high = mp(got_tin_high, ax(utape), utape, got_tin_high.sequent.right[0].right)
        got_tin_high = mp(got_tin_high, got_in_jv, jv_body.left, got_tin_high.sequent.right[0].right)
        got_tin_high = mp(got_tin_high, ax(succ_sa), succ_sa, got_tin_high.sequent.right[0].right)
        got_tin_high = mp(got_tin_high, got_plus_jv, jv_body.right, got_tin_high.sequent.right[0].right)
        got_tin_high = mp(got_tin_high, ax(num_one), num_one, Apply(tape_in,xv,one))
        c2_high = apply_thm(_tuo, [tape2, tape_in, a, one, xv, one])
        c2_high = mp(c2_high, ax(tu_tape2), tu_tape2, c2_high.sequent.right[0].right)
        c2_high = mp(c2_high, got_tin_high, Apply(tape_in,xv,one), c2_high.sequent.right[0].right)
        c2_high = mp(c2_high, ax(Not(Eq(xv,a))), Not(Eq(xv,a)), c2_high.sequent.right[0].right)
        c2_high = cut(ax(app_t2_xv_one), app_t2_xv_one, c2_high)
        c2_high = eel(c2_high, jv_body, jv)
        c2_high = cut(c2_high, Exists(jv, jv_body), got_pbe)
        # LEM In(xv,a) to combine c2_low and c2_high
        not_in_xva = Not(In(xv,a))
        l1 = [f for f in c2_low.sequent.left if not same(f, In(xv,a))]
        g1 = Proof(Sequent(l1, [not_in_xva, app_t2_xv_one]), 'not_right', [c2_low], principal=not_in_xva)
        ac = list(g1.sequent.left)
        for f in c2_high.sequent.left:
            if not same(f, not_in_xva) and not any(same(f, g) for g in ac): ac.append(f)
        c2 = Proof(Sequent(ac, [app_t2_xv_one]), 'cut',
            [weaken_to(g1, ac), weaken_to(c2_high, ac + [not_in_xva])], principal=not_in_xva)
        # LEM Eq(xv,a) to combine c1 and c2
        not_eq_xva = Not(Eq(xv,a))
        l2 = [f for f in c1.sequent.left if not same(f, Eq(xv,a))]
        g2 = Proof(Sequent(l2, [not_eq_xva, app_t2_xv_one]), 'not_right', [c1], principal=not_eq_xva)
        ac2 = list(g2.sequent.left)
        for f in c2.sequent.left:
            if not same(f, not_eq_xva) and not any(same(f, g) for g in ac2): ac2.append(f)
        return Proof(Sequent(ac2, [app_t2_xv_one]), 'cut',
            [weaken_to(g2, ac2), weaken_to(c2, ac2 + [not_eq_xva])], principal=not_eq_xva)

    # Helper: derive Apply(tape_in,xv,z) from beyond + ¬In(xv,hf)
    def derive_tape_in_xv_zero(xv, got_not_in_xvhf):
        got = apply_thm(got_beyond, [sa])
        got = mp(got, ax(succ_sa), succ_sa, got.sequent.right[0].right)
        got = apply_thm(got, [hf])
        got = mp(got, got_psbh, PlusDef(sa,b,hf), got.sequent.right[0].right)
        got = apply_thm(got, [xv])
        got = mp(got, got_not_in_xvhf, Not(In(xv,hf)), got.sequent.right[0].right)
        got = apply_thm(got, [z])
        got = mp(got, ax(num_z), num_z, Apply(tape_in,xv,z))
        return got

    # Helper: LEM on formula F to combine two proofs
    def lem_combine(got_with_f, got_with_not_f, f_formula, target):
        not_f = Not(f_formula)
        l = [ff for ff in got_with_f.sequent.left if not same(ff, f_formula)]
        g = Proof(Sequent(l, [not_f, target]), 'not_right', [got_with_f], principal=not_f)
        ac = list(g.sequent.left)
        for ff in got_with_not_f.sequent.left:
            if not same(ff, not_f) and not any(same(ff, gg) for gg in ac): ac.append(ff)
        return Proof(Sequent(ac, [target]), 'cut',
            [weaken_to(g, ac), weaken_to(got_with_not_f, ac + [not_f])], principal=not_f)

    # ====== Forward direction: ∀x,y. Apply(tf,x,y) → Apply(t2',x,y) ======
    xv = Var(postfix='_xfe'); yv = Var(postfix='_yfe')
    app_tf_xy = Apply(tf, xv, yv)
    app_t2p_xy = Apply(t2p, xv, yv)

    # Case A: In(xv,c)
    got_tf_xv_one = apply_thm(got_ones, [xv])
    got_tf_xv_one = mp(got_tf_xv_one, ax(In(xv,c)), In(xv,c), got_tf_xv_one.sequent.right[0].right)
    got_tf_xv_one = apply_thm(got_tf_xv_one, [one])
    got_tf_xv_one = mp(got_tf_xv_one, ax(num_one), num_one, Apply(tf,xv,one))
    got_y_eq_one = apply_thm(_fut, [tf, xv, yv, one])
    got_y_eq_one = mp(got_y_eq_one, got_func_tf, FuncDef(tf), got_y_eq_one.sequent.right[0].right)
    got_y_eq_one = mp(got_y_eq_one, ax(app_tf_xy), app_tf_xy, got_y_eq_one.sequent.right[0].right)
    got_y_eq_one = mp(got_y_eq_one, got_tf_xv_one, Apply(tf,xv,one), Eq(yv,one))
    got_not_xvc = derive_not_eq_xvc(xv)
    got_t2_xv_one = derive_tape2_xv_one(xv)
    got_t2p_xv_one = apply_thm(_tuo, [t2p, tape2, c, z, xv, one])
    got_t2p_xv_one = mp(got_t2p_xv_one, ax(t2p_body), t2p_body, got_t2p_xv_one.sequent.right[0].right)
    got_t2p_xv_one = mp(got_t2p_xv_one, got_t2_xv_one, Apply(tape2,xv,one), got_t2p_xv_one.sequent.right[0].right)
    got_t2p_xv_one = mp(got_t2p_xv_one, got_not_xvc, Not(Eq(xv,c)), got_t2p_xv_one.sequent.right[0].right)
    got_t2p_xv_one = cut(ax(Apply(t2p,xv,one)), Apply(t2p,xv,one), got_t2p_xv_one)
    got_eq_one_yv = apply_thm(_es, [yv, one], Eq(yv,one), Eq(one,yv), got_y_eq_one)
    got_caseA = apply_thm(_eavt, [t2p, xv, one, yv])
    got_caseA = mp(got_caseA, got_eq_one_yv, Eq(one,yv), got_caseA.sequent.right[0].right)
    got_caseA = mp(got_caseA, got_t2p_xv_one, Apply(t2p,xv,one), app_t2p_xy)
    print(f'tu_tf: forward case A (In(xv,c)) OK')

    # Case B: ¬In(xv,c)
    got_tf_xv_z = apply_thm(got_zeros, [xv])
    got_tf_xv_z = mp(got_tf_xv_z, ax(Not(In(xv,c))), Not(In(xv,c)), got_tf_xv_z.sequent.right[0].right)
    got_tf_xv_z = apply_thm(got_tf_xv_z, [z])
    got_tf_xv_z = mp(got_tf_xv_z, ax(num_z), num_z, Apply(tf,xv,z))
    got_y_eq_z = apply_thm(_fut, [tf, xv, yv, z])
    got_y_eq_z = mp(got_y_eq_z, got_func_tf, FuncDef(tf), got_y_eq_z.sequent.right[0].right)
    got_y_eq_z = mp(got_y_eq_z, ax(app_tf_xy), app_tf_xy, got_y_eq_z.sequent.right[0].right)
    got_y_eq_z = mp(got_y_eq_z, got_tf_xv_z, Apply(tf,xv,z), Eq(yv,z))

    # Sub-case Eq(xv,c): tape_update_at → Apply(t2p,c,z) → transfer
    got_t2p_c_z = apply_thm(_tua, [t2p, tape2, c, z, c, z])
    got_t2p_c_z = mp(got_t2p_c_z, ax(t2p_body), t2p_body, got_t2p_c_z.sequent.right[0].right)
    got_t2p_c_z = mp(got_t2p_c_z, apply_thm(eq_reflexive(), [c]), Eq(c,c), got_t2p_c_z.sequent.right[0].right)
    got_t2p_c_z = mp(got_t2p_c_z, apply_thm(eq_reflexive(), [z]), Eq(z,z), got_t2p_c_z.sequent.right[0].right)
    got_t2p_c_z = cut(ax(Apply(t2p,c,z)), Apply(t2p,c,z), got_t2p_c_z)
    got_eq_c_xv = apply_thm(_es, [xv, c], Eq(xv,c), Eq(c,xv), ax(Eq(xv,c)))
    got_t2p_xv_z_eq = apply_thm(_eat, [t2p, c, xv, z])
    got_t2p_xv_z_eq = mp(got_t2p_xv_z_eq, got_eq_c_xv, Eq(c,xv), got_t2p_xv_z_eq.sequent.right[0].right)
    got_t2p_xv_z_eq = mp(got_t2p_xv_z_eq, got_t2p_c_z, Apply(t2p,c,z), Apply(t2p,xv,z))

    # Sub-case ¬Eq(xv,c): beyond → tape_in(xv)=z → tape2(xv)=z → t2p(xv)=z
    got_not_xvhf = derive_not_in_xvhf(xv)
    got_tin_xv_z = derive_tape_in_xv_zero(xv, got_not_xvhf)
    got_not_xva = derive_not_eq_xva(xv, got_not_xvhf)
    got_t2_xv_z = apply_thm(_tuo, [tape2, tape_in, a, one, xv, z])
    got_t2_xv_z = mp(got_t2_xv_z, ax(tu_tape2), tu_tape2, got_t2_xv_z.sequent.right[0].right)
    got_t2_xv_z = mp(got_t2_xv_z, got_tin_xv_z, Apply(tape_in,xv,z), got_t2_xv_z.sequent.right[0].right)
    got_t2_xv_z = mp(got_t2_xv_z, got_not_xva, Not(Eq(xv,a)), got_t2_xv_z.sequent.right[0].right)
    got_t2_xv_z = cut(ax(Apply(tape2,xv,z)), Apply(tape2,xv,z), got_t2_xv_z)
    got_t2p_xv_z_neq = apply_thm(_tuo, [t2p, tape2, c, z, xv, z])
    got_t2p_xv_z_neq = mp(got_t2p_xv_z_neq, ax(t2p_body), t2p_body, got_t2p_xv_z_neq.sequent.right[0].right)
    got_t2p_xv_z_neq = mp(got_t2p_xv_z_neq, got_t2_xv_z, Apply(tape2,xv,z), got_t2p_xv_z_neq.sequent.right[0].right)
    got_t2p_xv_z_neq = mp(got_t2p_xv_z_neq, ax(Not(Eq(xv,c))), Not(Eq(xv,c)), got_t2p_xv_z_neq.sequent.right[0].right)
    got_t2p_xv_z_neq = cut(ax(Apply(t2p,xv,z)), Apply(t2p,xv,z), got_t2p_xv_z_neq)

    got_t2p_xv_z_full = lem_combine(got_t2p_xv_z_eq, got_t2p_xv_z_neq, Eq(xv,c), Apply(t2p,xv,z))
    got_eq_z_yv = apply_thm(_es, [yv, z], Eq(yv,z), Eq(z,yv), got_y_eq_z)
    got_caseB = apply_thm(_eavt, [t2p, xv, z, yv])
    got_caseB = mp(got_caseB, got_eq_z_yv, Eq(z,yv), got_caseB.sequent.right[0].right)
    got_caseB = mp(got_caseB, got_t2p_xv_z_full, Apply(t2p,xv,z), app_t2p_xy)
    print(f'tu_tf: forward case B (¬In(xv,c)) OK')

    got_fwd_one = lem_combine(got_caseA, got_caseB, In(xv,c), app_t2p_xy)
    # Discharge, close ∀
    imp_fwd = Implies(app_tf_xy, app_t2p_xy)
    l = [f for f in got_fwd_one.sequent.left if not same(f, app_tf_xy)]
    got_fwd_one = wl(got_fwd_one, app_tf_xy)
    got_fwd = Proof(Sequent(l, [imp_fwd]), 'implies_right', [got_fwd_one], principal=imp_fwd)
    fa_yv = Forall(yv, imp_fwd)
    got_fwd = Proof(Sequent(got_fwd.sequent.left, [fa_yv]), 'forall_right', [got_fwd], principal=fa_yv, term=yv)
    fa_xv = Forall(xv, fa_yv)
    got_fwd = Proof(Sequent(got_fwd.sequent.left, [fa_xv]), 'forall_right', [got_fwd], principal=fa_xv, term=xv)
    print(f'tu_tf: forward ∀ closed')

    # ====== Backward direction: ∀x,y. Apply(t2',x,y) → Apply(tf,x,y) ======
    xv2 = Var(postfix='_xbe'); yv2 = Var(postfix='_ybe')
    app_t2p_xy2 = Apply(t2p, xv2, yv2)
    app_tf_xy2 = Apply(tf, xv2, yv2)

    # Sub-case Eq(xv2,c): t2p(c)=z → yv2=z → ¬In(xv2,c) → Apply(tf,xv2,z) → transfer
    got_t2p_c_z_2 = apply_thm(_tua, [t2p, tape2, c, z, c, z])
    got_t2p_c_z_2 = mp(got_t2p_c_z_2, ax(t2p_body), t2p_body, got_t2p_c_z_2.sequent.right[0].right)
    got_t2p_c_z_2 = mp(got_t2p_c_z_2, apply_thm(eq_reflexive(), [c]), Eq(c,c), got_t2p_c_z_2.sequent.right[0].right)
    got_t2p_c_z_2 = mp(got_t2p_c_z_2, apply_thm(eq_reflexive(), [z]), Eq(z,z), got_t2p_c_z_2.sequent.right[0].right)
    got_t2p_c_z_2 = cut(ax(Apply(t2p,c,z)), Apply(t2p,c,z), got_t2p_c_z_2)
    got_eq_c_xv2 = apply_thm(_es, [xv2, c], Eq(xv2,c), Eq(c,xv2), ax(Eq(xv2,c)))
    got_t2p_xv2_z = apply_thm(_eat, [t2p, c, xv2, z])
    got_t2p_xv2_z = mp(got_t2p_xv2_z, got_eq_c_xv2, Eq(c,xv2), got_t2p_xv2_z.sequent.right[0].right)
    got_t2p_xv2_z = mp(got_t2p_xv2_z, got_t2p_c_z_2, Apply(t2p,c,z), Apply(t2p,xv2,z))
    got_yv2_eq_z = apply_thm(_fut, [t2p, xv2, yv2, z])
    got_yv2_eq_z = mp(got_yv2_eq_z, got_func_t2p, FuncDef(t2p), got_yv2_eq_z.sequent.right[0].right)
    got_yv2_eq_z = mp(got_yv2_eq_z, ax(app_t2p_xy2), app_t2p_xy2, got_yv2_eq_z.sequent.right[0].right)
    got_yv2_eq_z = mp(got_yv2_eq_z, got_t2p_xv2_z, Apply(t2p,xv2,z), Eq(yv2,z))
    # ¬In(xv2,c) from Eq(xv2,c) + omega_no_self
    got_not_cc = apply_thm(_onsm, [w, c])
    got_not_cc = mp(got_not_cc, ax(omega_w), omega_w, got_not_cc.sequent.right[0].right)
    got_not_cc = mp(got_not_cc, got_c_w, In(c,w), Not(In(c,c)))
    got_iff_xv2c = apply_thm(_esub, [xv2, c, c])
    got_iff_xv2c = mp(got_iff_xv2c, ax(Eq(xv2,c)), Eq(xv2,c), got_iff_xv2c.sequent.right[0].right)
    got_in_xv2c_cc = mp(apply_thm(iff_mp(In(xv2,c), In(c,c), []), [],
        Iff(In(xv2,c), In(c,c)), Implies(In(xv2,c), In(c,c)), got_iff_xv2c),
        ax(In(xv2,c)), In(xv2,c), In(c,c))
    not_in_xv2c = Not(In(xv2,c))
    bot = Proof(Sequent([In(c,c), Not(In(c,c))], []), 'not_left', [ax(In(c,c))], principal=Not(In(c,c)))
    bot = Proof(Sequent(bot.sequent.left, [not_in_xv2c]), 'weakening_right', [bot], principal=not_in_xv2c)
    bot = cut(bot, Not(In(c,c)), got_not_cc)
    bot = cut(bot, In(c,c), got_in_xv2c_cc)
    got_not_in_xv2c = lem_not(bot, In(xv2,c), not_in_xv2c)
    got_tf_xv2_z = apply_thm(got_zeros, [xv2])
    got_tf_xv2_z = mp(got_tf_xv2_z, got_not_in_xv2c, not_in_xv2c, got_tf_xv2_z.sequent.right[0].right)
    got_tf_xv2_z = apply_thm(got_tf_xv2_z, [z])
    got_tf_xv2_z = mp(got_tf_xv2_z, ax(num_z), num_z, Apply(tf,xv2,z))
    got_eq_z_yv2 = apply_thm(_es, [yv2, z], Eq(yv2,z), Eq(z,yv2), got_yv2_eq_z)
    got_bwd_eq = apply_thm(_eavt, [tf, xv2, z, yv2])
    got_bwd_eq = mp(got_bwd_eq, got_eq_z_yv2, Eq(z,yv2), got_bwd_eq.sequent.right[0].right)
    got_bwd_eq = mp(got_bwd_eq, got_tf_xv2_z, Apply(tf,xv2,z), app_tf_xy2)
    print(f'tu_tf: backward Eq(xv2,c) OK')

    # Sub-case ¬Eq(xv2,c): tape_update_other_rev → Apply(tape2,xv2,yv2)
    got_t2_xv2_yv2 = apply_thm(_tuor, [t2p, tape2, c, z, xv2, yv2])
    got_t2_xv2_yv2 = mp(got_t2_xv2_yv2, ax(t2p_body), t2p_body, got_t2_xv2_yv2.sequent.right[0].right)
    got_t2_xv2_yv2 = mp(got_t2_xv2_yv2, ax(app_t2p_xy2), app_t2p_xy2, got_t2_xv2_yv2.sequent.right[0].right)
    got_t2_xv2_yv2 = mp(got_t2_xv2_yv2, ax(Not(Eq(xv2,c))), Not(Eq(xv2,c)), got_t2_xv2_yv2.sequent.right[0].right)
    app_t2_xv2_yv2 = Apply(tape2, xv2, yv2)
    got_t2_xv2_yv2 = cut(ax(app_t2_xv2_yv2), app_t2_xv2_yv2, got_t2_xv2_yv2)

    # LEM In(xv2,c):
    # Case In(xv2,c): tape2(xv2)=one → yv2=one → tf(xv2)=one → transfer
    got_t2_xv2_one = derive_tape2_xv_one(xv2)
    got_yv2_eq_one = apply_thm(_fut, [tape2, xv2, yv2, one])
    got_yv2_eq_one = mp(got_yv2_eq_one, got_func_t2_inner, FuncDef(tape2), got_yv2_eq_one.sequent.right[0].right)
    got_yv2_eq_one = mp(got_yv2_eq_one, got_t2_xv2_yv2, app_t2_xv2_yv2, got_yv2_eq_one.sequent.right[0].right)
    got_yv2_eq_one = mp(got_yv2_eq_one, got_t2_xv2_one, Apply(tape2,xv2,one), Eq(yv2,one))
    got_tf_xv2_one = apply_thm(got_ones, [xv2])
    got_tf_xv2_one = mp(got_tf_xv2_one, ax(In(xv2,c)), In(xv2,c), got_tf_xv2_one.sequent.right[0].right)
    got_tf_xv2_one = apply_thm(got_tf_xv2_one, [one])
    got_tf_xv2_one = mp(got_tf_xv2_one, ax(num_one), num_one, Apply(tf,xv2,one))
    got_eq_one_yv2 = apply_thm(_es, [yv2, one], Eq(yv2,one), Eq(one,yv2), got_yv2_eq_one)
    got_bwd_in = apply_thm(_eavt, [tf, xv2, one, yv2])
    got_bwd_in = mp(got_bwd_in, got_eq_one_yv2, Eq(one,yv2), got_bwd_in.sequent.right[0].right)
    got_bwd_in = mp(got_bwd_in, got_tf_xv2_one, Apply(tf,xv2,one), app_tf_xy2)

    # Case ¬In(xv2,c): tape2(xv2)=z → yv2=z → tf(xv2)=z → transfer
    got_not_xv2hf = derive_not_in_xvhf(xv2)
    got_tin_xv2_z = derive_tape_in_xv_zero(xv2, got_not_xv2hf)
    got_not_xv2a = derive_not_eq_xva(xv2, got_not_xv2hf)
    got_t2_xv2_z = apply_thm(_tuo, [tape2, tape_in, a, one, xv2, z])
    got_t2_xv2_z = mp(got_t2_xv2_z, ax(tu_tape2), tu_tape2, got_t2_xv2_z.sequent.right[0].right)
    got_t2_xv2_z = mp(got_t2_xv2_z, got_tin_xv2_z, Apply(tape_in,xv2,z), got_t2_xv2_z.sequent.right[0].right)
    got_t2_xv2_z = mp(got_t2_xv2_z, got_not_xv2a, Not(Eq(xv2,a)), got_t2_xv2_z.sequent.right[0].right)
    got_t2_xv2_z = cut(ax(Apply(tape2,xv2,z)), Apply(tape2,xv2,z), got_t2_xv2_z)
    got_yv2_eq_z_notin = apply_thm(_fut, [tape2, xv2, yv2, z])
    got_yv2_eq_z_notin = mp(got_yv2_eq_z_notin, got_func_t2_inner, FuncDef(tape2), got_yv2_eq_z_notin.sequent.right[0].right)
    got_yv2_eq_z_notin = mp(got_yv2_eq_z_notin, got_t2_xv2_yv2, app_t2_xv2_yv2, got_yv2_eq_z_notin.sequent.right[0].right)
    got_yv2_eq_z_notin = mp(got_yv2_eq_z_notin, got_t2_xv2_z, Apply(tape2,xv2,z), Eq(yv2,z))
    got_tf_xv2_z_notin = apply_thm(got_zeros, [xv2])
    got_tf_xv2_z_notin = mp(got_tf_xv2_z_notin, ax(Not(In(xv2,c))), Not(In(xv2,c)), got_tf_xv2_z_notin.sequent.right[0].right)
    got_tf_xv2_z_notin = apply_thm(got_tf_xv2_z_notin, [z])
    got_tf_xv2_z_notin = mp(got_tf_xv2_z_notin, ax(num_z), num_z, Apply(tf,xv2,z))
    got_eq_z_yv2_notin = apply_thm(_es, [yv2, z], Eq(yv2,z), Eq(z,yv2), got_yv2_eq_z_notin)
    got_bwd_notin = apply_thm(_eavt, [tf, xv2, z, yv2])
    got_bwd_notin = mp(got_bwd_notin, got_eq_z_yv2_notin, Eq(z,yv2), got_bwd_notin.sequent.right[0].right)
    got_bwd_notin = mp(got_bwd_notin, got_tf_xv2_z_notin, Apply(tf,xv2,z), app_tf_xy2)

    got_bwd_neq = lem_combine(got_bwd_in, got_bwd_notin, In(xv2,c), app_tf_xy2)
    print(f'tu_tf: backward ¬Eq(xv2,c) OK')

    got_bwd_one = lem_combine(got_bwd_eq, got_bwd_neq, Eq(xv2,c), app_tf_xy2)
    # Discharge, close ∀
    imp_bwd = Implies(app_t2p_xy2, app_tf_xy2)
    l = [f for f in got_bwd_one.sequent.left if not same(f, app_t2p_xy2)]
    got_bwd_one = wl(got_bwd_one, app_t2p_xy2)
    got_bwd = Proof(Sequent(l, [imp_bwd]), 'implies_right', [got_bwd_one], principal=imp_bwd)
    fa_yv2 = Forall(yv2, imp_bwd)
    got_bwd = Proof(Sequent(got_bwd.sequent.left, [fa_yv2]), 'forall_right', [got_bwd], principal=fa_yv2, term=yv2)
    fa_xv2 = Forall(xv2, fa_yv2)
    got_bwd = Proof(Sequent(got_bwd.sequent.left, [fa_xv2]), 'forall_right', [got_bwd], principal=fa_xv2, term=xv2)
    print(f'tu_tf: backward ∀ closed')

    # ====== func_ext → Eq(tf, t2') ======
    _fe = func_ext()
    got_eq = apply_thm(_fe, [tf, t2p])
    got_eq = mp(got_eq, got_func_tf, FuncDef(tf), got_eq.sequent.right[0].right)
    got_eq = mp(got_eq, got_func_t2p, FuncDef(t2p), got_eq.sequent.right[0].right)
    got_eq = mp(got_eq, got_fwd, fa_xv, got_eq.sequent.right[0].right)
    got_eq = mp(got_eq, got_bwd, fa_xv2, Eq(tf, t2p))
    print(f'tu_tf: Eq(tf, t2p) OK')

    # ====== Transfer TapeUpdate via Iff chain ======
    tu_t2p_exp = t2p_body.expand()
    pv_tu = tu_t2p_exp.var
    iff_t2p = tu_t2p_exp.body
    in_pv_t2p = iff_t2p.left
    rhs_pv = iff_t2p.right
    in_pv_tf = In(pv_tu, tf)
    _et2 = eq_transfer_fn()
    got_iff_tf_t2p = apply_thm(_et2, [tf, t2p, pv_tu])
    got_iff_tf_t2p = mp(got_iff_tf_t2p, got_eq, Eq(tf,t2p), got_iff_tf_t2p.sequent.right[0].right)
    got_iff_t2p_rhs = fl(t2p_body, iff_t2p, pv_tu)
    # Chain: In(pv,tf) ↔ In(pv,t2p) ↔ RHS
    got_fwd_tf_t2p = apply_thm(iff_mp(in_pv_tf, in_pv_t2p, []), [],
        Iff(in_pv_tf, in_pv_t2p), Implies(in_pv_tf, in_pv_t2p), got_iff_tf_t2p)
    got_fwd_t2p_rhs = apply_thm(iff_mp(in_pv_t2p, rhs_pv, []), [],
        iff_t2p, Implies(in_pv_t2p, rhs_pv), got_iff_t2p_rhs)
    got_tf_to_rhs = mp(got_fwd_t2p_rhs, mp(got_fwd_tf_t2p, ax(in_pv_tf), in_pv_tf, in_pv_t2p),
        in_pv_t2p, rhs_pv)
    got_bwd_t2p_rhs = apply_thm(iff_mp_rev(in_pv_t2p, rhs_pv, []), [],
        iff_t2p, Implies(rhs_pv, in_pv_t2p), got_iff_t2p_rhs)
    got_bwd_tf_t2p = apply_thm(iff_mp_rev(in_pv_tf, in_pv_t2p, []), [],
        Iff(in_pv_tf, in_pv_t2p), Implies(in_pv_t2p, in_pv_tf), got_iff_tf_t2p)
    got_rhs_to_tf = mp(got_bwd_tf_t2p, mp(got_bwd_t2p_rhs, ax(rhs_pv), rhs_pv, in_pv_t2p),
        in_pv_t2p, in_pv_tf)
    iff_tf_rhs = Iff(in_pv_tf, rhs_pv)
    imp_tf_rhs = Implies(in_pv_tf, rhs_pv)
    imp_rhs_tf = Implies(rhs_pv, in_pv_tf)
    l_fwd = [f for f in got_tf_to_rhs.sequent.left if not same(f, in_pv_tf)]
    got_imp_fwd = Proof(Sequent(l_fwd, [imp_tf_rhs]), 'implies_right', [got_tf_to_rhs], principal=imp_tf_rhs)
    l_bwd = [f for f in got_rhs_to_tf.sequent.left if not same(f, rhs_pv)]
    got_imp_bwd = Proof(Sequent(l_bwd, [imp_rhs_tf]), 'implies_right', [got_rhs_to_tf], principal=imp_rhs_tf)
    got_iff_final = mp(apply_thm(iff_intro(in_pv_tf, rhs_pv, []), [],
        imp_tf_rhs, Implies(imp_rhs_tf, iff_tf_rhs), got_imp_fwd),
        got_imp_bwd, imp_rhs_tf, iff_tf_rhs)
    fa_pv = Forall(pv_tu, iff_tf_rhs)
    got_fa = Proof(Sequent(got_iff_final.sequent.left, [fa_pv]),
        'forall_right', [got_iff_final], principal=fa_pv, term=pv_tu)
    got_tu_tf = cut(ax(tu_tf_formula), tu_tf_formula, got_fa)
    got_tu_tf = eel(got_tu_tf, t2p_body, t2p)
    got_tu_tf = cut(got_tu_tf, Exists(t2p, t2p_body), got_tue)
    print(f'tu_tf: DONE — TapeUpdate(tf,tape2,c,z) derived')
    return got_tu_tf


# ============================================================
# tm_add_correct: chain Phase1P..Phase5P via TMReachesCompose
# ============================================================

def tm_add_correct():
    """TM addition correctness — matches add_goal() exactly.
    [Phase1P..Phase5P, TMReachesCompose, ZFC] |-
    ∀delta,q0,qH,hf,ssc,n,tf,cf,tin,z,c0,w,a,b,c.
      Omega(w) → In(a,w) → In(b,w) → Function(delta) → Function(tin) →
      delta_char → Num(q0,0) → Num(qH,1) → Num(z,0) →
      UnaryTape(tin,a,b) → TMConfig(c0,q0,z,tin) → Plus(a,b,c) →
      Successor(hf,c) → Successor(ssc,hf) → Successor(n,ssc) →
      UnaryOutput(tf,c) → TMConfig(cf,qH,hf,tf) →
      TMReaches(delta,c0,n,cf)
    """
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from core.proof import Proof, Sequent, same, _var_free_in_sequent
    from core.lang import Var, In, Implies, Forall
    from core.derived import Exists, And, Or, Iff, Eq
    from vocab.ordpair import OrdPair, Successor
    from theorems.arithmetic import num_exists
    from vocab.omega import Omega, Num
    from vocab.tm import TMConfig, TMTransition, TMStep, TapeUpdate, TMReaches
    from vocab.functions import Function as FuncDef, Apply
    from vocab.recursion import Plus as PlusDef
    from tm import UnaryTape, UnaryOutput, formalize, add_machine
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        or_intro_left, or_intro_right, or_elim, eq_reflexive,
        iff_mp, iff_mp_rev)

    # Use formalize to get delta_char with the right structure
    f = formalize(add_machine())

    # Goal variables — same as add_goal()
    delta, q0, qH = f['delta'], f['q0'], f['qH']
    a, b, c = Var(postfix='a'), Var(postfix='b'), Var(postfix='c')
    w = Var(postfix='w')
    tape_in = Var(postfix='tin')
    c0 = Var(postfix='c0')
    z = Var(postfix='z')
    hf = Var(postfix='hf')
    ssc = Var(postfix='ssc')
    n = Var(postfix='n')
    tf = Var(postfix='tf')
    cf = Var(postfix='cf')

    # Goal hypotheses
    omega_w = Omega(w)
    delta_char = f['delta_char']
    num_q0 = Num(q0, 0)
    num_qH = Num(qH, 1)
    num_z = Num(z, 0)
    utape = UnaryTape(tape_in, a, b)
    cfg_c0 = TMConfig(c0, q0, z, tape_in)
    plus_abc = PlusDef(a, b, c)
    succ_hf = Successor(hf, c)
    succ_ssc = Successor(ssc, hf)
    succ_n = Successor(n, ssc)
    unary_out = UnaryOutput(tf, c)
    cfg_cf = TMConfig(cf, qH, hf, tf)

    # === Extract individual transitions from delta_char ===
    # delta_char = And(And(And(And(And(t0,t1),t2),t3),t4),t5)
    # 6 transitions, left-associated And-tree
    got_dc = ax(delta_char)
    # Split: And(left5, t5) where left5 = And(And(And(And(t0,t1),t2),t3),t4)
    left5 = delta_char.left; t5_raw = delta_char.right
    got_left5 = apply_thm(and_elim_left(left5, t5_raw, []), [],
        delta_char, left5, got_dc)
    got_t5 = apply_thm(and_elim_right(left5, t5_raw, []), [],
        delta_char, t5_raw, got_dc)
    # Split left5: And(left4, t4)
    left4 = left5.left; t4_raw = left5.right
    got_left4 = apply_thm(and_elim_left(left4, t4_raw, []), [],
        left5, left4, got_left5)
    got_t4 = apply_thm(and_elim_right(left4, t4_raw, []), [],
        left5, t4_raw, got_left5)
    # Split left4: And(left3, t3)
    left3 = left4.left; t3_raw = left4.right
    got_left3 = apply_thm(and_elim_left(left3, t3_raw, []), [],
        left4, left3, got_left4)
    got_t3 = apply_thm(and_elim_right(left3, t3_raw, []), [],
        left4, t3_raw, got_left4)
    # Split left3: And(left2, t2)
    left2 = left3.left; t2_raw = left3.right
    got_left2 = apply_thm(and_elim_left(left2, t2_raw, []), [],
        left3, left2, got_left3)
    got_t2 = apply_thm(and_elim_right(left2, t2_raw, []), [],
        left3, t2_raw, got_left3)
    # Split left2: And(t0, t1)
    t0_raw = left2.left; t1_raw = left2.right
    got_t0 = apply_thm(and_elim_left(t0_raw, t1_raw, []), [],
        left2, t0_raw, got_left2)
    got_t1 = apply_thm(and_elim_right(t0_raw, t1_raw, []), [],
        left2, t1_raw, got_left2)
    # got_t0..got_t5: [delta_char] |- t_i (each a ∀-quantified transition)
    print(f'tm_add: delta_char decomposed into 6 transitions')

    # === Instantiate transitions to get TMTransition facts ===
    # Each t_i is: ∀s,r,w,d,sn. Num(s,_)→Num(r,_)→Num(w,_)→Num(d,_)→Num(sn,_)→TMTransition(delta,s,r,w,d,sn)
    # We need specific Var instances for the state/symbol params.
    # Create intermediate vars
    one = Var(postfix='one')
    zero = z  # Num(z,0) is a goal hypothesis, reuse it
    q1 = Var(postfix='q1')
    q2 = Var(postfix='q2')
    sa = Var(postfix='sa')
    tape2 = Var(postfix='t2')
    c1,c2,c3,c4 = Var(postfix='c1'), Var(postfix='c2'), Var(postfix='c3'), Var(postfix='c4')

    num_one = Num(one, 1)
    num_zero = num_z  # zero = z, reuse
    num_q1 = Num(q1, 2)
    num_q2 = Num(q2, 3)

    def inst_transition(got_raw, vars_list, nums_list):
        """Instantiate a ∀-quantified transition with specific vars and Num proofs."""
        got = got_raw
        for v in vars_list:
            got = apply_thm(got, [v])
        for num in nums_list:
            got = mp(got, ax(num), num, got.sequent.right[0].right)
        return got

    # t0: q0,1→1,R,q0
    trans_q0_1 = inst_transition(got_t0, [q0, one, one, one, q0],
        [num_q0, num_one, num_one, num_one, num_q0])

    # t1: q0,0→1,R,q1
    trans_q0_0 = inst_transition(got_t1, [q0, zero, one, one, q1],
        [num_q0, num_zero, num_one, num_one, num_q1])

    # t2: q1,1→1,R,q1
    trans_q1_1 = inst_transition(got_t2, [q1, one, one, one, q1],
        [num_q1, num_one, num_one, num_one, num_q1])

    # t3: q1,0→0,L,q2 (direction=0=zero)
    trans_q1_0 = inst_transition(got_t3, [q1, zero, zero, zero, q2],
        [num_q1, num_zero, num_zero, num_zero, num_q2])

    # t4: q2,1→0,R,qH
    trans_q2_1 = inst_transition(got_t4, [q2, one, zero, one, qH],
        [num_q2, num_one, num_zero, num_one, num_qH])

    # t5: q2,0→0,R,qH (edge case, not needed for main proof but let's derive it)
    # Skip for now — not used in the 5 phases
    print(f'tm_add: transitions instantiated')

    # === Intermediate formulas ===
    succ_sa = Successor(sa, a)
    tu_tape2 = TapeUpdate(tape2, tape_in, a, one)
    num_zero_z = Num(z, 0)  # alias for the goal's Num(z,0) — same as num_z but named differently
    tu_tf = TapeUpdate(tf, tape2, c, zero)
    cfg_c1 = TMConfig(c1, q0, a, tape_in)
    cfg_c2 = TMConfig(c2, q1, sa, tape2)
    cfg_c3 = TMConfig(c3, q1, hf, tape2)
    cfg_c4 = TMConfig(c4, q2, c, tape2)
    plus_sa_b_hf = PlusDef(sa, b, hf)
    tp = Var(postfix='tp')
    tape_read = Forall(tp, Implies(In(tp, w), Apply(tape2, tp, one)))
    tape2_hf_zero = Apply(tape2, hf, zero)
    tape2_c_one = Apply(tape2, c, one)
    plus_a_one_sa = PlusDef(a, one, sa)
    plus_hf_one_ssc = PlusDef(hf, one, ssc)
    plus_ssc_one_n = PlusDef(ssc, one, n)

    # Derive Apply(tape_in, a, zero) from tape_read_sep + UnaryTape + Num(zero,0)
    _trs = tape_read_sep()
    got_app_a_zero = apply_thm(_trs, [tape_in, a, b, zero])
    got_app_a_zero = mp(got_app_a_zero, ax(utape), utape, got_app_a_zero.sequent.right[0].right)
    got_app_a_zero = mp(got_app_a_zero, ax(num_z), num_z, Apply(tape_in, a, zero))

    # === Helper: mp through hypothesis list, using derived proofs where available ===
    derived_proofs = [trans_q0_1, trans_q0_0, trans_q1_1, trans_q1_0, trans_q2_1, got_app_a_zero]
    def mp_hyps(got, hyps):
        for h in hyps:
            src = None
            for dp in derived_proofs:
                if same(h, dp.sequent.right[0]):
                    src = dp
                    break
            if src is None:
                src = ax(h)
            try:
                got = mp(got, src, h, got.sequent.right[0].right)
            except ValueError:
                print(f'  mp FAIL: h={h}')
                print(f'  expected: {got.sequent.right[0].left}')
                raise
        return got

    # === Instantiate Phase1P..Phase5P ===
    # Phase1P ∀ order: d,q0,z,a,tape,w,one,b,c0,c1
    got_p1 = mp_hyps(
        apply_thm(ax(Phase1P()), [delta, q0, z, a, tape_in, w, one, b, c0, c1]),
        [trans_q0_1.sequent.right[0], omega_w, In(a,w), FuncDef(delta), FuncDef(tape_in),
         num_one, num_z, utape, cfg_c0, cfg_c1])

    # Phase2P ∀ order: d,q0,q1,a,sa,one,zero,tape,tape2,c1,c2
    got_p2 = mp_hyps(
        apply_thm(ax(Phase2P()), [delta, q0, q1, a, sa, one, zero, tape_in, tape2, c1, c2]),
        [trans_q0_0.sequent.right[0], FuncDef(delta), FuncDef(tape_in),
         num_one, num_zero, Apply(tape_in, a, zero), succ_sa, tu_tape2, cfg_c1, cfg_c2])

    # Phase3P ∀ order: d,q1,sa,b,pos,tape2,w,one,c1,c2
    # tape_read now: ∀j.In(j,b)→∀pp.Plus(sa,j,pp)→Apply(tape2,pp,one)
    tp = Var(postfix='tp')
    tpp = Var(postfix='tpp')
    tape_read = Forall(tp, Implies(In(tp,b), Forall(tpp, Implies(PlusDef(sa,tp,tpp), Apply(tape2,tpp,one)))))
    got_p3 = mp_hyps(
        apply_thm(ax(Phase3P()), [delta, q1, sa, b, hf, tape2, w, one, c2, c3]),
        [trans_q1_1.sequent.right[0], omega_w, In(b,w), In(sa,w),
         FuncDef(delta), FuncDef(tape2),
         num_one, tape_read,
         plus_sa_b_hf, cfg_c2, cfg_c3])

    # Phase4P ∀ order: d,q1,q2,hf,c,one,zero,tape2,c1,c2
    got_p4 = mp_hyps(
        apply_thm(ax(Phase4P()), [delta, q1, q2, hf, c, one, zero, tape2, c3, c4]),
        [trans_q1_0.sequent.right[0], FuncDef(delta), FuncDef(tape2),
         num_one, num_zero, succ_hf, tape2_hf_zero, cfg_c3, cfg_c4])

    # Phase5P ∀ order: d,q2,qH,c,hf,one,zero,tape2,tf,c1,c2
    got_p5 = mp_hyps(
        apply_thm(ax(Phase5P()), [delta, q2, qH, c, hf, one, zero, tape2, tf, c4, cf]),
        [trans_q2_1.sequent.right[0], FuncDef(delta), FuncDef(tape2),
         num_one, num_zero, succ_hf, tape2_c_one, tu_tf, cfg_c4, cfg_cf])
    print(f'tm_add: phases instantiated')

    # === Compose via TMReachesCompose ===
    comp = TMReachesCompose()

    got_12 = apply_thm(ax(comp), [delta, c0, c1, c2, a, one, sa, w])
    got_12 = mp(got_12, got_p1, got_p1.sequent.right[0], got_12.sequent.right[0].right)
    got_12 = mp(got_12, got_p2, got_p2.sequent.right[0], got_12.sequent.right[0].right)
    for h in [plus_a_one_sa, omega_w, In(a,w), In(one,w)]:
        got_12 = mp(got_12, ax(h), h, got_12.sequent.right[0].right)

    got_123 = apply_thm(ax(comp), [delta, c0, c2, c3, sa, b, hf, w])
    got_123 = mp(got_123, got_12, got_12.sequent.right[0], got_123.sequent.right[0].right)
    got_123 = mp(got_123, got_p3, got_p3.sequent.right[0], got_123.sequent.right[0].right)
    for h in [plus_sa_b_hf, omega_w, In(sa,w), In(b,w)]:
        got_123 = mp(got_123, ax(h), h, got_123.sequent.right[0].right)

    got_1234 = apply_thm(ax(comp), [delta, c0, c3, c4, hf, one, ssc, w])
    got_1234 = mp(got_1234, got_123, got_123.sequent.right[0], got_1234.sequent.right[0].right)
    got_1234 = mp(got_1234, got_p4, got_p4.sequent.right[0], got_1234.sequent.right[0].right)
    for h in [plus_hf_one_ssc, omega_w, In(hf,w), In(one,w)]:
        got_1234 = mp(got_1234, ax(h), h, got_1234.sequent.right[0].right)

    got_all = apply_thm(ax(comp), [delta, c0, c4, cf, ssc, one, n, w])
    got_all = mp(got_all, got_1234, got_1234.sequent.right[0], got_all.sequent.right[0].right)
    got_all = mp(got_all, got_p5, got_p5.sequent.right[0], got_all.sequent.right[0].right)
    for h in [plus_ssc_one_n, omega_w, In(ssc,w), In(one,w)]:
        got_all = mp(got_all, ax(h), h, got_all.sequent.right[0].right)
    # got_all: [lots of hyps] |- TMReaches(delta,c0,n,cf)
    print(f'tm_add: chain complete')

    # === Eliminate intermediate variables from left ===
    # Intermediate formulas on left that are NOT in add_goal:
    # cfg_c1, cfg_c2, cfg_c3, cfg_c4 (contain c1,c2,c3,c4)
    # succ_sa, tu_tape2, tu_tf (contain sa, tape2)
    # num_one, num_d1, num_zero, num_q1, num_q2, num_d0 (contain one,d1,zero,q1,q2,d0)
    # plus_a_one_sa, plus_sa_b_hf, plus_hf_one_ssc, plus_ssc_one_n
    # tape_read, tape2_hf_zero, tape2_c_one
    # In(sa,w), In(one,w), In(hf,w), In(ssc,w)
    # FuncDef(tape2)
    # All of these must be discharged (implies_right) then ∀-closed over intermediates.

    proof = got_all
    # RIGHT: TMReaches(delta,c0,n,cf) — no intermediate vars
    # LEFT: goal hyps + intermediate hyps + Phase*P + ZFC
    #
    # Intermediate vars on left: c1,c2,c3,c4 (in TMConfig only),
    #   one (in Num + Plus + In + transitions), q1,q2 (in Num + transitions),
    #   sa (in Successor + Plus + In), tape2 (in TapeUpdate + Function + tape stuff)
    #
    # Strategy: derive Plus/In/Function/tape from goal hyps (not ax),
    # then only Num/Successor/TMConfig remain as single-formula intermediates per var.
    # eel+cut each.
    #
    # But the chain already ran with ax() intermediates. So they're already on the left.
    # We need to CUT each ax'd intermediate with its derived proof.
    # cut(proof, F, derived_F) removes F from proof's left and adds derived_F's left.
    # If derived_F has only goal hyps + ZFC on left, the net effect is removing F.

    # Derive intermediate hypotheses from goal hyps
    from theorems.arithmetic import plus_zero_exists, plus_succ_right
    from theorems.omega import omega_succ_closed

    # Plus(a,one,sa) from plus_zero_exists + plus_succ_right
    _pze = plus_zero_exists()
    got_pza = apply_thm(_pze, [w, a, z])
    got_pza = mp(got_pza, ax(omega_w), omega_w, got_pza.sequent.right[0].right)
    got_pza = mp(got_pza, ax(In(a,w)), In(a,w), got_pza.sequent.right[0].right)
    got_pza = mp(got_pza, ax(num_z), num_z, got_pza.sequent.right[0].right)
    _psr = plus_succ_right()
    got_plus_a1s = apply_thm(_psr, [w, a, z, a, one, sa])
    got_plus_a1s = mp(got_plus_a1s, ax(omega_w), omega_w, got_plus_a1s.sequent.right[0].right)
    got_plus_a1s = mp(got_plus_a1s, ax(In(a,w)), In(a,w), got_plus_a1s.sequent.right[0].right)
    got_plus_a1s = mp(got_plus_a1s, ax(In(z,w)), In(z,w), got_plus_a1s.sequent.right[0].right)
    got_plus_a1s = mp(got_plus_a1s, got_pza, got_pza.sequent.right[0], got_plus_a1s.sequent.right[0].right)
    got_plus_a1s = mp(got_plus_a1s, ax(Successor(one,z)), Successor(one,z), got_plus_a1s.sequent.right[0].right)
    got_plus_a1s = mp(got_plus_a1s, ax(succ_sa), succ_sa, got_plus_a1s.sequent.right[0].right)
    # got_plus_a1s: [goal hyps, Succ(one,z), Succ(sa,a), In(z,w), ZFC] |- Plus(a,one,sa)

    # In(one,w) from omega_succ_closed
    _osc = omega_succ_closed()
    got_one_w = apply_thm(_osc, [w], omega_w,
        Forall(z, Implies(In(z,w), Forall(one, Implies(Successor(one,z), In(one,w))))), ax(omega_w))
    got_one_w = apply_thm(got_one_w, [z], In(z,w),
        Forall(one, Implies(Successor(one,z), In(one,w))), ax(In(z,w)))
    got_one_w = apply_thm(got_one_w, [one], Successor(one,z), In(one,w), ax(Successor(one,z)))

    # In(sa,w) from omega_succ_closed
    got_sa_w = apply_thm(_osc, [w], omega_w,
        Forall(a, Implies(In(a,w), Forall(sa, Implies(succ_sa, In(sa,w))))), ax(omega_w))
    got_sa_w = apply_thm(got_sa_w, [a], In(a,w),
        Forall(sa, Implies(succ_sa, In(sa,w))), ax(In(a,w)))
    got_sa_w = apply_thm(got_sa_w, [sa], succ_sa, In(sa,w), ax(succ_sa))

    # Plus(hf,one,ssc) from plus_zero_exists + plus_succ_right
    got_pzh = apply_thm(_pze, [w, hf, z])
    got_pzh = mp(got_pzh, ax(omega_w), omega_w, got_pzh.sequent.right[0].right)
    got_pzh = mp(got_pzh, ax(In(hf,w)), In(hf,w), got_pzh.sequent.right[0].right)
    got_pzh = mp(got_pzh, ax(num_z), num_z, got_pzh.sequent.right[0].right)
    got_plus_h1ss = apply_thm(_psr, [w, hf, z, hf, one, ssc])
    got_plus_h1ss = mp(got_plus_h1ss, ax(omega_w), omega_w, got_plus_h1ss.sequent.right[0].right)
    got_plus_h1ss = mp(got_plus_h1ss, ax(In(hf,w)), In(hf,w), got_plus_h1ss.sequent.right[0].right)
    got_plus_h1ss = mp(got_plus_h1ss, ax(In(z,w)), In(z,w), got_plus_h1ss.sequent.right[0].right)
    got_plus_h1ss = mp(got_plus_h1ss, got_pzh, got_pzh.sequent.right[0], got_plus_h1ss.sequent.right[0].right)
    got_plus_h1ss = mp(got_plus_h1ss, ax(Successor(one,z)), Successor(one,z), got_plus_h1ss.sequent.right[0].right)
    got_plus_h1ss = mp(got_plus_h1ss, ax(succ_ssc), succ_ssc, got_plus_h1ss.sequent.right[0].right)

    # Plus(ssc,one,n) similarly
    got_pzss = apply_thm(_pze, [w, ssc, z])
    got_pzss = mp(got_pzss, ax(omega_w), omega_w, got_pzss.sequent.right[0].right)
    got_pzss = mp(got_pzss, ax(In(ssc,w)), In(ssc,w), got_pzss.sequent.right[0].right)
    got_pzss = mp(got_pzss, ax(num_z), num_z, got_pzss.sequent.right[0].right)
    got_plus_ss1n = apply_thm(_psr, [w, ssc, z, ssc, one, n])
    got_plus_ss1n = mp(got_plus_ss1n, ax(omega_w), omega_w, got_plus_ss1n.sequent.right[0].right)
    got_plus_ss1n = mp(got_plus_ss1n, ax(In(ssc,w)), In(ssc,w), got_plus_ss1n.sequent.right[0].right)
    got_plus_ss1n = mp(got_plus_ss1n, ax(In(z,w)), In(z,w), got_plus_ss1n.sequent.right[0].right)
    got_plus_ss1n = mp(got_plus_ss1n, got_pzss, got_pzss.sequent.right[0], got_plus_ss1n.sequent.right[0].right)
    got_plus_ss1n = mp(got_plus_ss1n, ax(Successor(one,z)), Successor(one,z), got_plus_ss1n.sequent.right[0].right)
    got_plus_ss1n = mp(got_plus_ss1n, ax(succ_n), succ_n, got_plus_ss1n.sequent.right[0].right)


    # Plus(sa,b,hf) from plus_comm + plus_succ_right
    from theorems.arithmetic import plus_comm
    _pc = plus_comm()
    got_pba = apply_thm(_pc, [w, a, b, c])
    got_pba = mp(got_pba, ax(omega_w), omega_w, got_pba.sequent.right[0].right)
    got_pba = mp(got_pba, ax(In(a,w)), In(a,w), got_pba.sequent.right[0].right)
    got_pba = mp(got_pba, ax(In(b,w)), In(b,w), got_pba.sequent.right[0].right)
    got_pba = mp(got_pba, ax(plus_abc), plus_abc, got_pba.sequent.right[0].right)
    # Plus(b,a,c)
    got_pbsh = apply_thm(_psr, [w, b, a, c, sa, hf])
    got_pbsh = mp(got_pbsh, ax(omega_w), omega_w, got_pbsh.sequent.right[0].right)
    got_pbsh = mp(got_pbsh, ax(In(b,w)), In(b,w), got_pbsh.sequent.right[0].right)
    got_pbsh = mp(got_pbsh, ax(In(a,w)), In(a,w), got_pbsh.sequent.right[0].right)
    got_pbsh = mp(got_pbsh, got_pba, got_pba.sequent.right[0], got_pbsh.sequent.right[0].right)
    got_pbsh = mp(got_pbsh, ax(succ_sa), succ_sa, got_pbsh.sequent.right[0].right)
    got_pbsh = mp(got_pbsh, ax(succ_hf), succ_hf, got_pbsh.sequent.right[0].right)
    # Plus(b,sa,hf) → Plus(sa,b,hf) via comm
    got_psbh = apply_thm(_pc, [w, b, sa, hf])
    got_psbh = mp(got_psbh, ax(omega_w), omega_w, got_psbh.sequent.right[0].right)
    got_psbh = mp(got_psbh, ax(In(b,w)), In(b,w), got_psbh.sequent.right[0].right)
    got_psbh = mp(got_psbh, got_sa_w, In(sa,w), got_psbh.sequent.right[0].right)
    got_psbh = mp(got_psbh, got_pbsh, got_pbsh.sequent.right[0], got_psbh.sequent.right[0].right)
    # got_psbh: [...] |- Plus(sa,b,hf)
    if any(same(plus_sa_b_hf, f) for f in proof.sequent.left):
        proof = cut(proof, plus_sa_b_hf, got_psbh)

    # In(hf,w) — hf is a goal var, but In(hf,w) is NOT a goal hyp
    # Derive from Plus(sa,b,hf) via plus_val_in_omega
    from theorems.arithmetic import plus_val_in_omega
    _pvi = plus_val_in_omega()
    got_hf_w = apply_thm(_pvi, [w, sa, b, hf])
    got_hf_w = mp(got_hf_w, ax(omega_w), omega_w, got_hf_w.sequent.right[0].right)
    got_hf_w = mp(got_hf_w, got_sa_w, In(sa,w), got_hf_w.sequent.right[0].right)
    got_hf_w = mp(got_hf_w, ax(In(b,w)), In(b,w), got_hf_w.sequent.right[0].right)
    got_hf_w = mp(got_hf_w, got_psbh, plus_sa_b_hf, In(hf,w))

    # In(ssc,w) from omega_succ_closed + In(hf,w) + Successor(ssc,hf)
    got_ssc_w = apply_thm(_osc, [w], omega_w,
        Forall(hf, Implies(In(hf,w), Forall(ssc, Implies(succ_ssc, In(ssc,w))))), ax(omega_w))
    got_ssc_w = apply_thm(got_ssc_w, [hf], In(hf,w),
        Forall(ssc, Implies(succ_ssc, In(ssc,w))), got_hf_w)
    got_ssc_w = apply_thm(got_ssc_w, [ssc], succ_ssc, In(ssc,w), ax(succ_ssc))

    # In(z,w) from omega_contains_empty
    from theorems.omega import omega_contains_empty
    _oce = omega_contains_empty()
    got_z_w = apply_thm(_oce, [w], omega_w,
        Forall(z, Implies(num_z, In(z,w))), ax(omega_w))
    got_z_w = apply_thm(got_z_w, [z], num_z, In(z,w), ax(num_z))

    print(f'tm_add: intermediate derivations done')

    # === Cut each ax'd intermediate from the left with its derived proof ===
    # This removes the ax'd formula and adds the derived proof's left (goal hyps, already there)
    derived_cuts = [
        (plus_a_one_sa, got_plus_a1s),
        (In(one,w), got_one_w),
        (In(sa,w), got_sa_w),
        (plus_hf_one_ssc, got_plus_h1ss),
        (plus_ssc_one_n, got_plus_ss1n),
        (In(hf,w), got_hf_w),
        (In(ssc,w), got_ssc_w),
        (In(z,w), got_z_w),
    ]
    for formula, derived in derived_cuts:
        if any(same(formula, f) for f in proof.sequent.left):
            proof = cut(proof, formula, derived)

    # Now remaining intermediates on left (single formula per var):
    #   Num(one,1), Successor(one,z) — var: one
    #   Num(q1,2) — var: q1
    #   Num(q2,3) — var: q2
    #   Successor(sa,a) — var: sa (succ_sa)
    #   TMConfig(c1,...) — var: c1
    #   TMConfig(c2,...) — var: c2 (also has q1, sa, tape2 — but those should be gone?)
    #   TMConfig(c3,...) — var: c3 (also has q1, tape2)
    #   TMConfig(c4,...) — var: c4 (also has q2, tape2)
    #   TapeUpdate(tape2,...) — var: tape2 (also has one)
    #   Function(tape2) — var: tape2
    #   tape_read — var: tape2, one
    #   tape2_hf_zero — var: tape2
    #   tape2_c_one — var: tape2, one
    #   tu_tf — var: tape2
    #   plus_sa_b_hf — var: sa (already cut above? No, this was ax'd in Phase3P mp)

    # Hmm, there are still many multi-var formulas. Let me check which are actually on the left.
    from core.proof import _var_free_in_sequent
    int_vars_list = [('one',one), ('q1',q1), ('q2',q2), ('sa',sa), ('tape2',tape2),
                     ('c1',c1), ('c2',c2), ('c3',c3), ('c4',c4)]
    for vname, v in int_vars_list:
        count = sum(1 for f in proof.sequent.left if _var_free_in_sequent(v, Sequent([f], [])))
        if count > 0:
            formulas = [str(f)[:60] for f in proof.sequent.left if _var_free_in_sequent(v, Sequent([f], []))]
            unique_f = []
            for f in proof.sequent.left:
                if _var_free_in_sequent(v, Sequent([f], [])):
                    if not any(same(f, u) for u in unique_f):
                        unique_f.append(f)
            print(f'  {vname}: {len(unique_f)} unique formulas, {count} total')

    # eel+cut for configs (c1-c4 only in TMConfig)
    _ce = config_exists()
    for cfg_var, cfg_formula in [(c1, cfg_c1), (c2, cfg_c2), (c3, cfg_c3), (c4, cfg_c4)]:
        if any(same(cfg_formula, f) for f in proof.sequent.left):
            other_left = [f for f in proof.sequent.left if not same(f, cfg_formula)]
            if not any(_var_free_in_sequent(cfg_var, Sequent([f], [])) for f in other_left):
                proof = eel(proof, cfg_formula, cfg_var)
                # ∃cfg_var. TMConfig(cfg_var,state,head,tape) from config_exists
                got_ex_cfg = apply_thm(_ce, [cfg_formula.state, cfg_formula.head, cfg_formula.tape])
                proof = cut(proof, Exists(cfg_var, cfg_formula), got_ex_cfg)
            else:
                print(f'  SKIP eel {cfg_var}: free in other left formulas')

    # eel+cut for q1, q2 (only in Num)
    for var, num_k in [(q1, 2), (q2, 3)]:
        num_formula = Num(var, num_k)
        if any(same(num_formula, f) for f in proof.sequent.left):
            other_left = [f for f in proof.sequent.left if not same(f, num_formula)]
            if not any(_var_free_in_sequent(var, Sequent([f], [])) for f in other_left):
                proof = eel(proof, num_formula, var)
                got_ex_num = num_exists(num_k)
                proof = cut(proof, Exists(var, num_formula), got_ex_num)
            else:
                print(f'  SKIP eel {var}: free in other left formulas')

    # Cut remaining intermediate formulas with derived proofs
    # Remaining: Num(one,1), Successor(one,z), Successor(sa,a), TapeUpdate(tape2,...),
    #   Function(tape2), tape_read, Plus(sa,b,hf), Apply(tape2,hf,z), Apply(tape2,c,one),
    #   TapeUpdate(tf,tape2,c,z)


    # TapeUpdate(tape2,...), Function(tape2), tape_read, tape values, tu_tf:
    # These are all tape2-related. Need tape_update_exists, tape_update_function, 
    # tape_read theorems from backup. For NOW, just discharge as implies + ∀tape2.
    # Then eel sa from Successor(sa,a), one from Num(one,1)+Successor(one,z).

    # First: eel sa from Successor(sa,a) — sa now only in Successor(sa,a) (Plus gone)
    if any(same(succ_sa, f) for f in proof.sequent.left):
        other_left = [f for f in proof.sequent.left if not same(f, succ_sa)]
        if not any(_var_free_in_sequent(sa, Sequent([f], [])) for f in other_left):
            proof = eel(proof, succ_sa, sa)
            from theorems.sets import successor_exists as _se
            got_ex_sa = apply_thm(_se(), [a], concl=Exists(sa, succ_sa))
            proof = cut(proof, Exists(sa, succ_sa), got_ex_sa)
        else:
            print(f'  SKIP eel sa: still free in other formulas')

    # === Cut each tape2 formula with derived proof ===
    # Each derived proof has [TapeUpdate(tape2,...), goal_hyps, ZFC] on left.
    # When cut, TapeUpdate stays (already there), the specific formula is removed.

    # Function(tape2) from TapeUpdate + Function(tape_in)
    _tuf = tape_update_function()
    got_func_t2 = apply_thm(_tuf, [tape2, tape_in, a, one])
    got_func_t2 = mp(got_func_t2, ax(tu_tape2), tu_tape2, got_func_t2.sequent.right[0].right)
    got_func_t2 = mp(got_func_t2, ax(FuncDef(tape_in)), FuncDef(tape_in), FuncDef(tape2))
    # [tu_tape2, Function(tape_in), ZFC] |- Function(tape2)
    proof = cut(proof, FuncDef(tape2), got_func_t2)

    # tape_read: ∀j.In(j,b)→∀pp.Plus(sa,j,pp)→Apply(tape2,pp,one)
    # Derive from tape_read_high + tape_update_other:
    #   tape_read_high: UnaryTape(tin,a,b) → In(j,b) → Succ(sa,a) → Plus(sa,j,pp) → Num(one,1) → Apply(tin,pp,one)
    #   tape_update_other: TapeUpdate(t2,t,pos,val) → Apply(t,x,y) → Not(Eq(x,pos)) → Apply(t2,x,y)
    # Need: Apply(tape_in,pp,one) + Not(Eq(pp,a)) → Apply(tape2,pp,one)
    # Not(Eq(pp,a)): pp = sa+j where j∈b. pp ≥ sa = S(a) > a. So pp ≠ a.
    # This requires omega ordering. For now, derive tape_read from goal hyps + ax for the hard parts.
    # TODO: prove Not(Eq(pp,a)) from omega ordering.
    # For now: ax(tape_read) — it's the Phase3P hypothesis, provable from tape structure.

    # tape2_hf_zero: Apply(tape2,hf,zero) — tape2 reads 0 at hf (past all ones)
    # tape2_c_one: Apply(tape2,c,one) — tape2 reads 1 at c (last 1 in second group)
    # tu_tf: TapeUpdate(tf,tape2,c,zero) — tf = tape2 with position c erased
    # These all need tape semantics proofs. TODO: derive from UnaryTape + TapeUpdate.

    # For now: cut tape_read, tape2_hf_zero, tape2_c_one, tu_tf with ax-based derived proofs.
    # These ax() proofs have the formula on both sides, so cut is a no-op for the left.
    # But we can cut the DUPLICATE copies (from mp_hyps) — eel removes ALL copies.
    # After cutting Function(tape2) and Plus(sa,b,hf), tape2 formulas remaining:
    # tu_tape2, tape_read, tape2_hf_zero, tape2_c_one, tu_tf (5 formulas)
    # All have tape2 free. Can't eel tape2 until all are gone.
    # Must cut each with a derived proof that has tape2 on left only via tu_tape2.

    # tape_read: derived from tape_read_high + tape_update_other
    # tape_read_high: ∀tape,a,b,j,sa,pos,one. UnaryTape → In(j,b) → Succ(sa,a) → Plus(sa,j,pos) → Num(one,1) → Apply(tape,pos,one)
    # tape_update_other: ∀t2,t,pos,val,x,y. TapeUpdate(t2,t,pos,val) → Apply(t,x,y) → Not(Eq(x,pos)) → Apply(t2,x,y)
    _trh = tape_read_high()
    _tuo = tape_update_other()

    # Build: [UnaryTape, In(j,b), Succ(sa,a), Plus(sa,j,pp), Num(one,1), TapeUpdate(tape2,tin,a,one), Not(Eq(pp,a))]
    #   |- Apply(tape2,pp,one)
    jv = Var(postfix='jv')
    ppv = Var(postfix='ppv')
    got_read_tin = apply_thm(_trh, [tape_in, a, b, jv, sa, ppv, one])
    got_read_tin = mp(got_read_tin, ax(utape), utape, got_read_tin.sequent.right[0].right)
    got_read_tin = mp(got_read_tin, ax(In(jv,b)), In(jv,b), got_read_tin.sequent.right[0].right)
    got_read_tin = mp(got_read_tin, ax(succ_sa), succ_sa, got_read_tin.sequent.right[0].right)
    got_read_tin = mp(got_read_tin, ax(PlusDef(sa,jv,ppv)), PlusDef(sa,jv,ppv), got_read_tin.sequent.right[0].right)
    got_read_tin = mp(got_read_tin, ax(num_one), num_one, got_read_tin.sequent.right[0].right)
    # [UnaryTape, In(jv,b), Succ(sa,a), Plus(sa,jv,ppv), Num(one,1)] |- Apply(tape_in,ppv,one)

    got_read_t2 = apply_thm(_tuo, [tape2, tape_in, a, one, ppv, one])
    got_read_t2 = mp(got_read_t2, ax(tu_tape2), tu_tape2, got_read_t2.sequent.right[0].right)
    got_read_t2 = mp(got_read_t2, got_read_tin, Apply(tape_in,ppv,one), got_read_t2.sequent.right[0].right)
    got_read_t2 = mp(got_read_t2, ax(Not(Eq(ppv,a))), Not(Eq(ppv,a)), Apply(tape2,ppv,one))
    # [tu_tape2, UnaryTape, ..., Not(Eq(ppv,a))] |- Apply(tape2,ppv,one)

    # Discharge Plus(sa,jv,ppv), Not(Eq(ppv,a)), close ∀ppv
    imp_plus_pp = Implies(PlusDef(sa,jv,ppv), Apply(tape2,ppv,one))
    # Need to discharge Not(Eq(ppv,a)) — TODO: derive from omega ordering
    # For now: discharge as hypothesis (will be an extra formula on the left)
    # Actually: let me skip the Not(Eq(ppv,a)) issue and just ax the tape_read for now.
    # The tape_read formula has jv and ppv bound by ∀ inside, so it won't block eel for tape2
    # IF I can derive it with only [tu_tape2, goal_hyps] on the left.
    # But Not(Eq(ppv,a)) is hard to derive without omega ordering theorems.

    # PRAGMATIC: derive tape_read from [tu_tape2, UnaryTape, Succ(sa,a), Num(one,1), Not(Eq(ppv,a))]
    # The Not(Eq(ppv,a)) will stay on left — but it's ∀-bound (ppv is closed by forall_right).
    # Actually ppv is free. Let me discharge it.
    got_tr = got_read_t2
    # Discharge Not(Eq(ppv,a)) — as implies_right
    not_eq = Not(Eq(ppv,a))
    got_tr = wl(got_tr, not_eq)
    imp_not = Implies(not_eq, got_tr.sequent.right[0])
    left_not = [f for f in got_tr.sequent.left if not same(f, not_eq)]
    got_tr = Proof(Sequent(left_not, [imp_not]), 'implies_right', [got_tr], principal=imp_not)
    # Discharge Plus(sa,jv,ppv)
    plus_jv = PlusDef(sa,jv,ppv)
    got_tr = wl(got_tr, plus_jv)
    imp_pjv = Implies(plus_jv, got_tr.sequent.right[0])
    left_pjv = [f for f in got_tr.sequent.left if not same(f, plus_jv)]
    got_tr = Proof(Sequent(left_pjv, [imp_pjv]), 'implies_right', [got_tr], principal=imp_pjv)
    # Close ∀ppv
    fa_ppv = Forall(ppv, imp_pjv)
    got_tr = Proof(Sequent(got_tr.sequent.left, [fa_ppv]),
        'forall_right', [got_tr], principal=fa_ppv, term=ppv)
    # Discharge In(jv,b)
    got_tr = wl(got_tr, In(jv,b))
    imp_jb = Implies(In(jv,b), fa_ppv)
    left_jb = [f for f in got_tr.sequent.left if not same(f, In(jv,b))]
    got_tr = Proof(Sequent(left_jb, [imp_jb]), 'implies_right', [got_tr], principal=imp_jb)
    # Close ∀jv
    fa_jv = Forall(jv, imp_jb)
    got_tr = Proof(Sequent(got_tr.sequent.left, [fa_jv]),
        'forall_right', [got_tr], principal=fa_jv, term=jv)
    # got_tr: [tu_tape2, UnaryTape, Succ(sa,a), Num(one,1), ZFC] |- ∀j.In(j,b)→∀pp.(Plus→Not→Apply)
    # But this has an extra Not(Eq) inside — doesn't match tape_read exactly.
    # tape_read = ∀j.In(j,b)→∀pp.Plus(sa,j,pp)→Apply(tape2,pp,one)
    # got_tr = ∀j.In(j,b)→∀pp.Plus(sa,j,pp)→Not(Eq(pp,a))→Apply(tape2,pp,one)
    # These are DIFFERENT — got_tr has an extra Not hypothesis.
    # So this derived proof can't cut tape_read directly.

    # Don't need Not(Eq(pp,a))! Use LEM: Eq(pp,a) ∨ Not(Eq(pp,a)).
    # Case Eq(pp,a): tape_update_at gives Apply(tape2,pp,one) (wrote one at a, pp=a)
    # Case Not(Eq(pp,a)): tape_update_other + tape_read_high gives Apply(tape2,pp,one)
    # Both produce the same Apply(tape2,pp,one). Cut on Not(Eq(pp,a)).

    _tua = tape_update_at()

    # Case 1: Eq(pp,a) → Apply(tape2,pp,one) via tape_update_at
    from theorems.logic import eq_reflexive as _er
    got_case1 = apply_thm(_tua, [tape2, tape_in, a, one, ppv, one])
    got_case1 = mp(got_case1, ax(tu_tape2), tu_tape2, got_case1.sequent.right[0].right)
    got_case1 = mp(got_case1, ax(Eq(ppv,a)), Eq(ppv,a), got_case1.sequent.right[0].right)
    got_eq_oo = apply_thm(_er(), [one])
    got_case1 = mp(got_case1, got_eq_oo, Eq(one,one), got_case1.sequent.right[0].right)
    # got_case1 has Apply(tape2,ppv,one) on right — but it returns ∃p.And(OrdPair,In)
    # which IS Apply(tape2,ppv,one). Let me check.
    app_t2_pp_one = Apply(tape2, ppv, one)
    got_case1 = cut(ax(app_t2_pp_one), app_t2_pp_one, got_case1)
    # [Eq(ppv,a), tu_tape2, Pairing] |- Apply(tape2,ppv,one)

    # Case 2: Not(Eq(ppv,a)) → Apply(tape2,ppv,one)
    got_case2 = apply_thm(_tuo, [tape2, tape_in, a, one, ppv, one])
    got_case2 = mp(got_case2, ax(tu_tape2), tu_tape2, got_case2.sequent.right[0].right)
    got_case2 = mp(got_case2, got_read_tin, Apply(tape_in,ppv,one), got_case2.sequent.right[0].right)
    not_eq = Not(Eq(ppv,a))
    got_case2 = mp(got_case2, ax(not_eq), not_eq, got_case2.sequent.right[0].right)
    got_case2 = cut(ax(app_t2_pp_one), app_t2_pp_one, got_case2)
    # [Not(Eq(ppv,a)), tu_tape2, UnaryTape, ...] |- Apply(tape2,ppv,one)

    # LEM: combine via not_right + cut
    # Case1: [Eq(ppv,a), ctx1] |- Apply. not_right: [ctx1] |- Not(Eq), Apply.
    # Case2: [Not(Eq), ctx2] |- Apply. Cut on Not(Eq): [ctx1,ctx2] |- Apply.
    left_c1_clean = [f for f in got_case1.sequent.left if not same(f, Eq(ppv,a))]
    got_lem = Proof(Sequent(left_c1_clean, [not_eq, app_t2_pp_one]),
        'not_right', [got_case1], principal=not_eq)
    from tactics import weaken_to
    all_ctx = list(got_lem.sequent.left)
    for f in got_case2.sequent.left:
        if not same(f, not_eq) and not any(same(f, g) for g in all_ctx):
            all_ctx.append(f)
    got_tape2_read = Proof(Sequent(all_ctx, [app_t2_pp_one]), 'cut',
        [weaken_to(got_lem, all_ctx),
         weaken_to(got_case2, all_ctx + [not_eq])],
        principal=not_eq)
    # [tu_tape2, UnaryTape, Succ(sa,a), Plus(sa,jv,ppv), Num(one,1), Pairing] |- Apply(tape2,ppv,one)
    print(f'tm_add: tape2 read at pp via LEM: OK')

    # Discharge Plus, close ∀ppv, discharge In(jv,b), close ∀jv → tape_read formula
    plus_jv = PlusDef(sa,jv,ppv)
    imp_plus_pp = Implies(plus_jv, app_t2_pp_one)
    left_pjv = [f for f in got_tape2_read.sequent.left if not same(f, plus_jv)]
    got_tape2_read = Proof(Sequent(left_pjv, [imp_plus_pp]),
        'implies_right', [got_tape2_read], principal=imp_plus_pp)
    fa_ppv = Forall(ppv, imp_plus_pp)
    got_tape2_read = Proof(Sequent(got_tape2_read.sequent.left, [fa_ppv]),
        'forall_right', [got_tape2_read], principal=fa_ppv, term=ppv)
    in_jv_b = In(jv,b)
    imp_jb = Implies(in_jv_b, fa_ppv)
    left_jb = [f for f in got_tape2_read.sequent.left if not same(f, in_jv_b)]
    got_tape2_read = Proof(Sequent(left_jb, [imp_jb]),
        'implies_right', [got_tape2_read], principal=imp_jb)
    fa_jv = Forall(jv, imp_jb)
    got_tape2_read = Proof(Sequent(got_tape2_read.sequent.left, [fa_jv]),
        'forall_right', [got_tape2_read], principal=fa_jv, term=jv)
    # got_tape2_read: [...] |- tape_read
    proof = cut(proof, tape_read, got_tape2_read)
    print(f'tm_add: tape_read cut')

    # === tape2_hf_zero: Apply(tape2,hf,z) ===
    # 1. Or(Eq(a,c), In(a,c)) from plus_geq (ax for now — needs Plus uniqueness to extract from ∃)
    or_eq_in_ac = Or(Eq(a,c), In(a,c))
    # 2. In(a,hf) from Successor(hf,c) + Or(Eq(a,c), In(a,c))
    or_a_c = Or(In(a,c), Eq(a,c))
    iff_a_hf = Iff(In(a,hf), or_a_c)
    got_iff_ahf = fl(succ_hf, iff_a_hf, a)
    # Rearrange Or
    got_or_rearranged2 = apply_thm(or_intro_right(In(a,c), Eq(a,c), []), [], Eq(a,c), or_a_c, ax(Eq(a,c)))
    got_or_rearranged3 = apply_thm(or_intro_left(In(a,c), Eq(a,c), []), [], In(a,c), or_a_c, ax(In(a,c)))
    oe2 = or_elim(Eq(a,c), In(a,c), or_a_c, [])
    imp_eq_or2 = Implies(Eq(a,c), or_a_c)
    got_imp_eq2 = Proof(Sequent([], [imp_eq_or2]), 'implies_right', [got_or_rearranged2], principal=imp_eq_or2)
    imp_in_or2 = Implies(In(a,c), or_a_c)
    got_imp_in2 = Proof(Sequent([], [imp_in_or2]), 'implies_right', [got_or_rearranged3], principal=imp_in_or2)
    got_or_ac = apply_thm(oe2, [], or_eq_in_ac,
        Implies(imp_eq_or2, Implies(imp_in_or2, or_a_c)), ax(or_eq_in_ac))
    got_or_ac = mp(got_or_ac, got_imp_eq2, imp_eq_or2, Implies(imp_in_or2, or_a_c))
    got_or_ac = mp(got_or_ac, got_imp_in2, imp_in_or2, or_a_c)
    # [Or(Eq(a,c),In(a,c))] |- Or(In(a,c),Eq(a,c))
    got_in_a_hf = mp(apply_thm(iff_mp_rev(In(a,hf), or_a_c, []), [],
        iff_a_hf, Implies(or_a_c, In(a,hf)), got_iff_ahf),
        got_or_ac, or_a_c, In(a,hf))
    # 3. Not(Eq(hf,a)) from In(a,hf) + omega
    from theorems.sets import eq_transfer as _et_fn, omega_no_self_membership as _onsm_fn
    _onsm = _onsm_fn()
    got_not_aa = apply_thm(_onsm, [w, a])
    got_not_aa = mp(got_not_aa, ax(omega_w), omega_w, got_not_aa.sequent.right[0].right)
    got_not_aa = mp(got_not_aa, ax(In(a,w)), In(a,w), Not(In(a,a)))
    _et = _et_fn()
    got_iff_ha = apply_thm(_et, [hf, a, a])
    got_iff_ha = mp(got_iff_ha, ax(Eq(hf,a)), Eq(hf,a), got_iff_ha.sequent.right[0].right)
    got_in_a_a = mp(apply_thm(iff_mp(In(a,hf), In(a,a), []), [],
        Iff(In(a,hf), In(a,a)), Implies(In(a,hf), In(a,a)), got_iff_ha),
        got_in_a_hf, In(a,hf), In(a,a))
    # Bottom + (A→¬A)→¬A
    not_eq_hf_a = Not(Eq(hf,a))
    got_bot = Proof(Sequent([In(a,a), Not(In(a,a))], []), 'not_left', [ax(In(a,a))], principal=Not(In(a,a)))
    got_bot = Proof(Sequent(got_bot.sequent.left, [not_eq_hf_a]), 'weakening_right', [got_bot], principal=not_eq_hf_a)
    got_bot = wl(got_bot, Eq(hf,a))
    got_bot = cut(got_bot, Not(In(a,a)), got_not_aa)
    got_bot = cut(got_bot, In(a,a), got_in_a_a)
    rest_hfa = [f for f in got_bot.sequent.left if not same(f, Eq(hf,a))]
    imp_eq_neq = Implies(Eq(hf,a), not_eq_hf_a)
    got_imp_hfa = Proof(Sequent(rest_hfa, [imp_eq_neq]), 'implies_right', [got_bot], principal=imp_eq_neq)
    got_lem_hfa = Proof(Sequent([], [not_eq_hf_a, Eq(hf,a)]), 'not_right', [ax(Eq(hf,a))], principal=not_eq_hf_a)
    got_use_hfa = Proof(Sequent([imp_eq_neq], [not_eq_hf_a]), 'implies_left', [got_lem_hfa, ax(not_eq_hf_a)], principal=imp_eq_neq)
    got_not_hfa = cut(got_use_hfa, imp_eq_neq, got_imp_hfa)
    # 4. Apply(tape_in,hf,z) from UnaryTape beyond
    # UnaryTape = And(func, And(low, And(sep, And(high, beyond))))
    exp_ut = utape.expand()
    r0 = exp_ut.right  # And(low, And(sep, And(high, beyond)))
    got_r0 = apply_thm(and_elim_right(exp_ut.left, r0, []), [], utape, r0, ax(utape))
    r1 = r0.right  # And(sep, And(high, beyond))
    got_r1 = apply_thm(and_elim_right(r0.left, r1, []), [], r0, r1, got_r0)
    r2 = r1.right  # And(high, beyond)
    got_r2 = apply_thm(and_elim_right(r1.left, r2, []), [], r1, r2, got_r1)
    got_beyond = apply_thm(and_elim_right(r2.left, r2.right, []), [], r2, r2.right, got_r2)
    got_tin_hf = apply_thm(got_beyond, [sa])
    got_tin_hf = mp(got_tin_hf, ax(succ_sa), succ_sa, got_tin_hf.sequent.right[0].right)
    got_tin_hf = apply_thm(got_tin_hf, [hf])
    got_tin_hf = mp(got_tin_hf, got_psbh, plus_sa_b_hf, got_tin_hf.sequent.right[0].right)
    got_tin_hf = apply_thm(got_tin_hf, [hf])
    got_not_hfhf = apply_thm(_onsm, [w, hf])
    got_not_hfhf = mp(got_not_hfhf, ax(omega_w), omega_w, got_not_hfhf.sequent.right[0].right)
    got_not_hfhf = mp(got_not_hfhf, got_hf_w, In(hf,w), Not(In(hf,hf)))
    got_tin_hf = mp(got_tin_hf, got_not_hfhf, Not(In(hf,hf)), got_tin_hf.sequent.right[0].right)
    got_tin_hf = apply_thm(got_tin_hf, [z])
    got_tin_hf = mp(got_tin_hf, ax(num_z), num_z, got_tin_hf.sequent.right[0].right)
    # 5. Apply(tape2,hf,z) from tape_update_other + Not(Eq(hf,a))
    got_t2_hf = apply_thm(_tuo, [tape2, tape_in, a, one, hf, z])
    got_t2_hf = mp(got_t2_hf, ax(tu_tape2), tu_tape2, got_t2_hf.sequent.right[0].right)
    got_t2_hf = mp(got_t2_hf, got_tin_hf, Apply(tape_in,hf,z), got_t2_hf.sequent.right[0].right)
    got_t2_hf = mp(got_t2_hf, got_not_hfa, not_eq_hf_a, got_t2_hf.sequent.right[0].right)
    got_t2_hf = cut(ax(tape2_hf_zero), tape2_hf_zero, got_t2_hf)
    proof = cut(proof, tape2_hf_zero, got_t2_hf)
    print(f'tm_add: tape2_hf_zero cut')

    # === tape2_c_one: Apply(tape2,c,one) via LEM ===
    app_t2_c_one = Apply(tape2, c, one)
    got_c1_case1 = apply_thm(_tua, [tape2, tape_in, a, one, c, one])
    got_c1_case1 = mp(got_c1_case1, ax(tu_tape2), tu_tape2, got_c1_case1.sequent.right[0].right)
    got_c1_case1 = mp(got_c1_case1, ax(Eq(c,a)), Eq(c,a), got_c1_case1.sequent.right[0].right)
    got_eq_oo2 = apply_thm(eq_reflexive(), [one])
    got_c1_case1 = mp(got_c1_case1, got_eq_oo2, Eq(one,one), got_c1_case1.sequent.right[0].right)
    got_c1_case1 = cut(ax(app_t2_c_one), app_t2_c_one, got_c1_case1)

    # Case2: Not(Eq(c,a)) — derive Apply(tape2,c,one) via full chain
    from theorems.sets import omega_pred as _op_fn, succ_injection as _si_fn, omega_transitive as _ot_fn
    from theorems.arithmetic import plus_pred as _pp_fn, plus_zero_right as _pzr_fn, plus_val_in_omega as _pvi_fn
    from theorems.recursion import eq_apply_transfer as _eat_fn
    not_eq_ca = Not(Eq(c,a))

    _op2 = _op_fn()
    got_op2 = apply_thm(_op2, [w, b])
    got_op2 = mp(got_op2, ax(omega_w), omega_w, got_op2.sequent.right[0].right)
    got_op2 = mp(got_op2, ax(In(b,w)), In(b,w), got_op2.sequent.right[0].right)
    or_pred = got_op2.sequent.right[0]
    empty_b = or_pred.left; ex_k = or_pred.right

    # Case Empty(b) → contradiction → Apply(tape2,c,one)
    _pzr3 = _pzr_fn()
    got_ca = apply_thm(_pzr3, [w, a, b, c])
    got_ca = mp(got_ca, ax(omega_w), omega_w, got_ca.sequent.right[0].right)
    got_ca = mp(got_ca, ax(In(a,w)), In(a,w), got_ca.sequent.right[0].right)
    got_ca = mp(got_ca, ax(empty_b), empty_b, got_ca.sequent.right[0].right)
    got_ca = mp(got_ca, ax(plus_abc), plus_abc, Eq(c,a))
    got_bot_b0 = Proof(Sequent([Eq(c,a), not_eq_ca], []), 'not_left', [ax(Eq(c,a))], principal=not_eq_ca)
    got_bot_b0 = Proof(Sequent(got_bot_b0.sequent.left, [app_t2_c_one]), 'weakening_right', [got_bot_b0], principal=app_t2_c_one)
    got_bot_b0 = cut(got_bot_b0, Eq(c,a), got_ca)

    # Case ∃k: full derivation chain
    kv2 = Var(postfix='kv2')
    succ_b_k = Successor(b, kv2); in_k_b = In(kv2, b)
    and_sk = And(succ_b_k, in_k_b)
    got_succ_k = apply_thm(and_elim_left(succ_b_k, in_k_b, []), [], and_sk, succ_b_k, ax(and_sk))
    got_in_k = apply_thm(and_elim_right(succ_b_k, in_k_b, []), [], and_sk, in_k_b, ax(and_sk))
    _ot = _ot_fn()
    got_kv2_w = apply_thm(_ot, [w, b, kv2])
    got_kv2_w = mp(got_kv2_w, ax(omega_w), omega_w, got_kv2_w.sequent.right[0].right)
    got_kv2_w = mp(got_kv2_w, ax(In(b,w)), In(b,w), got_kv2_w.sequent.right[0].right)
    got_kv2_w = mp(got_kv2_w, got_in_k, in_k_b, In(kv2,w))
    _pp2 = _pp_fn()
    got_pp = apply_thm(_pp2, [w, sa, kv2, b, hf])
    got_pp = mp(got_pp, ax(omega_w), omega_w, got_pp.sequent.right[0].right)
    got_pp = mp(got_pp, got_succ_k, succ_b_k, got_pp.sequent.right[0].right)
    got_pp = mp(got_pp, ax(In(sa,w)), In(sa,w), got_pp.sequent.right[0].right)
    got_pp = mp(got_pp, got_kv2_w, In(kv2,w), got_pp.sequent.right[0].right)
    got_pp = mp(got_pp, got_psbh, plus_sa_b_hf, got_pp.sequent.right[0].right)
    pp_var = got_pp.sequent.right[0].var
    pp_body = got_pp.sequent.right[0].body
    got_plus_skq = apply_thm(and_elim_left(pp_body.left, pp_body.right, []), [], pp_body, pp_body.left, ax(pp_body))
    got_succ_hfq = apply_thm(and_elim_right(pp_body.left, pp_body.right, []), [], pp_body, pp_body.right, ax(pp_body))
    _si = _si_fn()
    _pvi2 = _pvi_fn()
    got_ppv_w = apply_thm(_pvi2, [w, sa, kv2, pp_var])
    got_ppv_w = mp(got_ppv_w, ax(omega_w), omega_w, got_ppv_w.sequent.right[0].right)
    got_ppv_w = mp(got_ppv_w, ax(In(sa,w)), In(sa,w), got_ppv_w.sequent.right[0].right)
    got_ppv_w = mp(got_ppv_w, got_kv2_w, In(kv2,w), got_ppv_w.sequent.right[0].right)
    got_ppv_w = mp(got_ppv_w, got_plus_skq, pp_body.left, In(pp_var,w))
    got_c_w = apply_thm(_pvi2, [w, a, b, c])
    got_c_w = mp(got_c_w, ax(omega_w), omega_w, got_c_w.sequent.right[0].right)
    got_c_w = mp(got_c_w, ax(In(a,w)), In(a,w), got_c_w.sequent.right[0].right)
    got_c_w = mp(got_c_w, ax(In(b,w)), In(b,w), got_c_w.sequent.right[0].right)
    got_c_w = mp(got_c_w, ax(plus_abc), plus_abc, In(c,w))
    got_si = apply_thm(_si, [hf, w, pp_var, c])
    got_si = mp(got_si, got_succ_hfq, pp_body.right, got_si.sequent.right[0].right)
    got_si = mp(got_si, ax(succ_hf), succ_hf, got_si.sequent.right[0].right)
    got_si = mp(got_si, ax(omega_w), omega_w, got_si.sequent.right[0].right)
    got_si = mp(got_si, got_ppv_w, In(pp_var,w), got_si.sequent.right[0].right)
    got_si = mp(got_si, got_c_w, In(c,w), Eq(pp_var, c))
    got_tin_ppv = apply_thm(_trh, [tape_in, a, b, kv2, sa, pp_var, one])
    got_tin_ppv = mp(got_tin_ppv, ax(utape), utape, got_tin_ppv.sequent.right[0].right)
    got_tin_ppv = mp(got_tin_ppv, got_in_k, in_k_b, got_tin_ppv.sequent.right[0].right)
    got_tin_ppv = mp(got_tin_ppv, ax(succ_sa), succ_sa, got_tin_ppv.sequent.right[0].right)
    got_tin_ppv = mp(got_tin_ppv, got_plus_skq, pp_body.left, got_tin_ppv.sequent.right[0].right)
    got_tin_ppv = mp(got_tin_ppv, ax(num_one), num_one, got_tin_ppv.sequent.right[0].right)
    _eat = _eat_fn()
    got_tin_c = apply_thm(_eat, [tape_in, pp_var, c, one])
    got_tin_c = mp(got_tin_c, got_si, Eq(pp_var,c), got_tin_c.sequent.right[0].right)
    got_tin_c = mp(got_tin_c, got_tin_ppv, Apply(tape_in,pp_var,one), Apply(tape_in,c,one))
    got_c1_inner = apply_thm(_tuo, [tape2, tape_in, a, one, c, one])
    got_c1_inner = mp(got_c1_inner, ax(tu_tape2), tu_tape2, got_c1_inner.sequent.right[0].right)
    got_c1_inner = mp(got_c1_inner, got_tin_c, Apply(tape_in,c,one), got_c1_inner.sequent.right[0].right)
    got_c1_inner = mp(got_c1_inner, ax(not_eq_ca), not_eq_ca, got_c1_inner.sequent.right[0].right)
    got_c1_inner = cut(ax(app_t2_c_one), app_t2_c_one, got_c1_inner)
    got_c1_inner = eel(got_c1_inner, pp_body, pp_var)
    got_c1_inner = cut(got_c1_inner, got_pp.sequent.right[0], got_pp)
    got_c1_inner = eel(got_c1_inner, and_sk, kv2)

    # or_elim: combine Empty case + ∃k case
    imp_empty = Implies(empty_b, app_t2_c_one)
    left_empty = [f for f in got_bot_b0.sequent.left if not same(f, empty_b)]
    got_imp_empty = Proof(Sequent(left_empty, [imp_empty]), 'implies_right', [got_bot_b0], principal=imp_empty)
    imp_exk = Implies(Exists(kv2, and_sk), app_t2_c_one)
    left_exk = [f for f in got_c1_inner.sequent.left if not same(f, Exists(kv2, and_sk))]
    got_imp_exk = Proof(Sequent(left_exk, [imp_exk]), 'implies_right', [got_c1_inner], principal=imp_exk)
    oe3 = or_elim(empty_b, ex_k, app_t2_c_one, [])
    got_c1_combined = apply_thm(oe3, [], or_pred,
        Implies(imp_empty, Implies(imp_exk, app_t2_c_one)), ax(or_pred))
    got_c1_combined = mp(got_c1_combined, got_imp_empty, imp_empty, Implies(imp_exk, app_t2_c_one))
    got_c1_combined = mp(got_c1_combined, got_imp_exk, imp_exk, app_t2_c_one)
    got_c1_case2 = cut(got_c1_combined, or_pred, got_op2)
    left_c1_clean = [f for f in got_c1_case1.sequent.left if not same(f, Eq(c,a))]
    got_lem_c = Proof(Sequent(left_c1_clean, [not_eq_ca, app_t2_c_one]), 'not_right', [got_c1_case1], principal=not_eq_ca)
    all_ctx_c = list(got_lem_c.sequent.left)
    for f in got_c1_case2.sequent.left:
        if not same(f, not_eq_ca) and not any(same(f, g) for g in all_ctx_c):
            all_ctx_c.append(f)
    got_t2_c = Proof(Sequent(all_ctx_c, [app_t2_c_one]), 'cut',
        [weaken_to(got_lem_c, all_ctx_c), weaken_to(got_c1_case2, all_ctx_c + [not_eq_ca])],
        principal=not_eq_ca)
    proof = cut(proof, tape2_c_one, got_t2_c)
    print(f'tm_add: tape2_c_one cut')

    # Cut In(sa,w) re-introduced by tape2_c_one derivation
    if any(same(In(sa,w), f) for f in proof.sequent.left):
        proof = cut(proof, In(sa,w), got_sa_w)

    # === Cut Or(Eq(a,c),In(a,c)) with plus_geq + plus_val_unique ===
    from theorems.arithmetic import plus_geq, plus_val_unique
    # plus_geq: ∃cv. And(Plus(a,b,cv), Or(Eq(a,cv), In(a,cv)))
    _pg = plus_geq()
    got_pg = apply_thm(_pg, [w, a, b])
    got_pg = mp(got_pg, ax(omega_w), omega_w, got_pg.sequent.right[0].right)
    got_pg = mp(got_pg, ax(In(a,w)), In(a,w), got_pg.sequent.right[0].right)
    got_pg = mp(got_pg, ax(In(b,w)), In(b,w), got_pg.sequent.right[0].right)
    # |- ∃cv. And(Plus(a,b,cv), Or(Eq(a,cv), In(a,cv)))
    # Open ∃cv
    pg_cv = got_pg.sequent.right[0].var
    pg_body = got_pg.sequent.right[0].body
    got_plus_cv = apply_thm(and_elim_left(pg_body.left, pg_body.right, []), [],
        pg_body, pg_body.left, ax(pg_body))
    got_or_cv = apply_thm(and_elim_right(pg_body.left, pg_body.right, []), [],
        pg_body, pg_body.right, ax(pg_body))
    # [pg_body] |- Plus(a,b,cv), Or(Eq(a,cv),In(a,cv))

    # plus_val_unique: Plus(a,b,c) ∧ Plus(a,b,cv) → c = cv
    _pvu = plus_val_unique()
    got_eq_c_cv = apply_thm(_pvu, [w, a, b, c, pg_cv])
    got_eq_c_cv = mp(got_eq_c_cv, ax(omega_w), omega_w, got_eq_c_cv.sequent.right[0].right)
    got_eq_c_cv = mp(got_eq_c_cv, ax(In(a,w)), In(a,w), got_eq_c_cv.sequent.right[0].right)
    got_eq_c_cv = mp(got_eq_c_cv, ax(In(b,w)), In(b,w), got_eq_c_cv.sequent.right[0].right)
    got_eq_c_cv = mp(got_eq_c_cv, ax(plus_abc), plus_abc, got_eq_c_cv.sequent.right[0].right)
    got_eq_c_cv = mp(got_eq_c_cv, got_plus_cv, pg_body.left, Eq(c, pg_cv))

    # Transfer Or(Eq(a,cv),In(a,cv)) → Or(Eq(a,c),In(a,c)) via Eq(c,cv)
    from theorems.logic import eq_symmetric as _es_fn
    from theorems.sets import eq_transfer as _et_fn2
    _es = _es_fn()
    got_eq_cv_c = apply_thm(_es, [c, pg_cv], Eq(c, pg_cv), Eq(pg_cv, c), got_eq_c_cv)
    # Eq(cv,c) → Iff(In(a,cv), In(a,c))
    _et2 = _et_fn2()
    got_iff_ac = apply_thm(_et2, [pg_cv, c, a])
    got_iff_ac = mp(got_iff_ac, got_eq_cv_c, Eq(pg_cv,c), got_iff_ac.sequent.right[0].right)
    # Eq(cv,c) → Iff(Eq(a,cv), Eq(a,c)) — via eq_substitution
    from theorems.logic import eq_substitution as _esub_fn
    _esub = _esub_fn()
    # Actually eq_substitution gives Eq(a,b)→Iff(In(a,z),In(b,z)). I need Eq(cv,c)→Iff(Eq(a,cv),Eq(a,c)).
    # That's: Eq(cv,c) → (a=cv ↔ a=c). Use eq_substitution on Eq(a,_):
    # Eq(cv,c) → Iff(In(cv,z), In(c,z)) for membership. For equality: different.
    # Actually: Eq(a,cv) ∧ Eq(cv,c) → Eq(a,c) via eq_transitive.
    #           Eq(a,c) ∧ Eq(c,cv)=Eq(cv,c)^-1 → Eq(a,cv).
    # Or_elim on Or(Eq(a,cv), In(a,cv)):
    #   Eq(a,cv): Eq(a,cv) + Eq(cv,c) → Eq(a,c). Or left.
    #   In(a,cv): In(a,cv) + Iff(In(a,cv),In(a,c)) → In(a,c). Or right.
    from theorems.logic import eq_transitive as _et_fn3
    _etr = _et_fn3()
    or_ac = Or(Eq(a,c), In(a,c))
    # Case Eq(a,cv) → Eq(a,c)
    got_eq_a_c = apply_thm(_etr, [a, pg_cv, c])
    got_eq_a_c = mp(got_eq_a_c, ax(Eq(a,pg_cv)), Eq(a,pg_cv), got_eq_a_c.sequent.right[0].right)
    got_eq_a_c = mp(got_eq_a_c, got_eq_cv_c, Eq(pg_cv,c), Eq(a,c))
    got_or_eq = apply_thm(or_intro_left(Eq(a,c), In(a,c), []), [], Eq(a,c), or_ac, got_eq_a_c)
    # Case In(a,cv) → In(a,c)
    got_in_a_c = mp(apply_thm(iff_mp(In(a,pg_cv), In(a,c), []), [],
        Iff(In(a,pg_cv), In(a,c)), Implies(In(a,pg_cv), In(a,c)), got_iff_ac),
        ax(In(a,pg_cv)), In(a,pg_cv), In(a,c))
    got_or_in = apply_thm(or_intro_right(Eq(a,c), In(a,c), []), [], In(a,c), or_ac, got_in_a_c)
    # or_elim
    or_cv = Or(Eq(a,pg_cv), In(a,pg_cv))
    oe3 = or_elim(Eq(a,pg_cv), In(a,pg_cv), or_ac, [])
    imp_eq_or3 = Implies(Eq(a,pg_cv), or_ac)
    got_imp_eq3 = Proof(Sequent([f for f in got_or_eq.sequent.left if not same(f, Eq(a,pg_cv))],
        [imp_eq_or3]), 'implies_right', [got_or_eq], principal=imp_eq_or3)
    imp_in_or3 = Implies(In(a,pg_cv), or_ac)
    got_imp_in3 = Proof(Sequent([f for f in got_or_in.sequent.left if not same(f, In(a,pg_cv))],
        [imp_in_or3]), 'implies_right', [got_or_in], principal=imp_in_or3)
    got_or_final = apply_thm(oe3, [], or_cv,
        Implies(imp_eq_or3, Implies(imp_in_or3, or_ac)), ax(or_cv))
    got_or_final = mp(got_or_final, got_imp_eq3, imp_eq_or3, Implies(imp_in_or3, or_ac))
    got_or_final = mp(got_or_final, got_imp_in3, imp_in_or3, or_ac)
    # [Or(Eq(a,cv),In(a,cv)), ...] |- Or(Eq(a,c),In(a,c))
    got_or_final = cut(got_or_final, or_cv, got_or_cv)
    # eel cv from pg_body, cut with got_pg
    got_or_final = eel(got_or_final, pg_body, pg_cv)
    got_or_final = cut(got_or_final, got_pg.sequent.right[0], got_pg)
    # |- Or(Eq(a,c),In(a,c)) from goal hyps
    or_eq_in_ac = Or(Eq(a,c), In(a,c))
    proof = cut(proof, or_eq_in_ac, got_or_final)
    print(f'tm_add: Or(Eq(a,c),In(a,c)) cut')

    # === Derive TapeUpdate(tf,tape2,c,z) via func_ext ===
    got_tu_tf = derive_tu_tf(
        tf=tf, tape2=tape2, tape_in=tape_in, c=c, z=z, a=a, b=b, w=w,
        sa=sa, one=one, hf=hf,
        utape=utape, tu_tape2=tu_tape2, unary_out=unary_out,
        succ_sa=succ_sa, succ_hf=succ_hf, plus_abc=plus_abc,
        num_one=num_one, num_z=num_z, omega_w=omega_w,
        got_sa_w=got_sa_w, got_hf_w=got_hf_w, got_psbh=got_psbh, got_c_w=got_c_w)
    proof = cut(proof, tu_tf, got_tu_tf)
    print(f'tm_add: tu_tf cut')

    # === eel+cut for sa (only in Successor(sa,a) now) ===
    if any(same(succ_sa, f) for f in proof.sequent.left):
        other_left = [f for f in proof.sequent.left if not same(f, succ_sa)]
        if not any(_var_free_in_sequent(sa, Sequent([f], [])) for f in other_left):
            proof = eel(proof, succ_sa, sa)
            from theorems.sets import successor_exists as _se
            got_ex_sa = apply_thm(_se(), [a], concl=Exists(sa, succ_sa))
            proof = cut(proof, Exists(sa, succ_sa), got_ex_sa)
            print(f'tm_add: sa eel+cut done')
        else:
            print(f'tm_add: SKIP eel sa — still free elsewhere')

    # === eel+cut for tape2 (only in TapeUpdate(tape2,tape_in,a,one) now) ===
    if any(same(tu_tape2, f) for f in proof.sequent.left):
        other_left = [f for f in proof.sequent.left if not same(f, tu_tape2)]
        if not any(_var_free_in_sequent(tape2, Sequent([f], [])) for f in other_left):
            proof = eel(proof, tu_tape2, tape2)
            got_ex_t2 = apply_thm(tape_update_exists(), [tape_in, a, one])
            proof = cut(proof, Exists(tape2, tu_tape2), got_ex_t2)
            print(f'tm_add: tape2 eel+cut done')
        else:
            print(f'tm_add: SKIP eel tape2 — still free elsewhere')

    # === eel+cut for one (in Num(one,1) and Successor(one,z)) ===
    # Combine the two formulas into And, eel one, cut with existence proof
    succ_one_z = Successor(one, z)
    and_one = And(num_one, succ_one_z)
    if any(same(num_one, f) for f in proof.sequent.left) and \
       any(same(succ_one_z, f) for f in proof.sequent.left):
        # Cut Num(one,1) with And left component
        got_num_from_and = apply_thm(and_elim_left(num_one, succ_one_z, []), [],
            and_one, num_one, ax(and_one))
        proof = cut(proof, num_one, got_num_from_and)
        # Cut Successor(one,z) with And right component
        got_succ_from_and = apply_thm(and_elim_right(num_one, succ_one_z, []), [],
            and_one, succ_one_z, ax(and_one))
        proof = cut(proof, succ_one_z, got_succ_from_and)
        # Now And(num_one, succ_one_z) on left. eel one.
        other_left = [f for f in proof.sequent.left if not same(f, and_one)]
        if not any(_var_free_in_sequent(one, Sequent([f], [])) for f in other_left):
            proof = eel(proof, and_one, one)
            # Prove ∃one. And(Num(one,1), Successor(one,z)) from Num(z,0) + ZFC.
            # Num(one,1).expand() = ∀v. Num(v,0) → Successor(one,v).
            # Instantiate v=z: Num(z,0) → Successor(one,z). mp with Num(z,0).
            from theorems.arithmetic import num_exists
            got_ex_num = num_exists(1)
            nv = got_ex_num.sequent.right[0].var
            num_nv = Num(nv, 1)
            succ_nv_z2 = Successor(nv, z)
            num_nv_exp = num_nv.expand()
            inst_body = Implies(Num(z,0), succ_nv_z2)
            got_succ_nv = fl(num_nv, inst_body, z)
            got_succ_nv = mp(got_succ_nv, ax(num_z), num_z, succ_nv_z2)
            and_nv = And(num_nv, succ_nv_z2)
            got_and_nv = mp(apply_thm(and_intro(num_nv, succ_nv_z2, []), [],
                num_nv, Implies(succ_nv_z2, and_nv), ax(num_nv)),
                got_succ_nv, succ_nv_z2, and_nv)
            got_ex_and = eir(got_and_nv, and_nv, nv, nv)
            got_ex_and = eel(got_ex_and, num_nv, nv)
            got_ex_and = cut(got_ex_and, Exists(nv, num_nv), got_ex_num)
            proof = cut(proof, Exists(one, and_one), got_ex_and)
            print(f'tm_add: one eel+cut done')
        else:
            print(f'tm_add: SKIP eel one — still free elsewhere')

    # Debug: print remaining non-axiom formulas
    from core.zfc import ZFCAxiom
    non_ax = [f for f in proof.sequent.left
              if not isinstance(f, (ZFCAxiom, Phase1P, Phase2P, Phase3P, Phase4P, Phase5P, TMReachesCompose))]
    print(f'tm_add: {len(non_ax)} non-axiom formulas remain before discharge')
    for f in non_ax:
        print(f'  {str(f)[:80]}')

    # Discharge goal hypotheses in add_goal's order
    goal_hyps = [omega_w, In(a,w), In(b,w), FuncDef(delta), FuncDef(tape_in),
                 delta_char, num_q0, num_qH, num_z, utape, cfg_c0, plus_abc,
                 succ_hf, succ_ssc, succ_n, unary_out, cfg_cf]
    for hyp in reversed(goal_hyps):
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left_new = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left_new, [imp]), 'implies_right', [proof], principal=imp)

    # Close ∀ over goal vars in add_goal's order
    for v in [c, b, a, w, c0, z, tape_in, cf, tf, n, ssc, hf, qH, q0, delta]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        try:
            proof = Proof(Sequent(proof.sequent.left, [fa]),
                'forall_right', [proof], principal=fa, term=v)
        except ValueError:
            for f in proof.sequent.left:
                if _var_free_in_sequent(v, Sequent([f], [])):
                    print(f'  forall_right BLOCKED: {v} free in {str(f)[:60]}')
            break

    proof.name = 'tm_add_correct'
    return proof

# ============================================================
# Helper theorems moved from tm_backup.py
# ============================================================


def config_elim():
    """TMConfig elimination: from TMConfig and OrdPair(inner,h,tape), get OrdPair(c,q,inner).
    |- forall c, q, h, tape, inner.
         TMConfig(c,q,h,tape) -> OrdPair(inner,h,tape) -> OrdPair(c,q,inner)"""
    from core.proof import Proof, Sequent, same
    from tactics import fl, mp, ax
    c, q, h, tape, inner = Var(), Var(), Var(), Var(), Var()

    cfg = TMConfig(c, q, h, tape)
    op_inner = OrdPair(inner, h, tape)
    op_c = OrdPair(c, q, inner)

    # cfg expands to Forall(v, OrdPair(v,h,tape) -> OrdPair(c,q,v))
    # Instantiate with inner: OrdPair(inner,h,tape) -> OrdPair(c,q,inner)
    target = Implies(op_inner, op_c)
    p0 = fl(cfg, target, inner)
    # [cfg] |- OrdPair(inner,h,tape) -> OrdPair(c,q,inner)

    p1 = mp(p0, ax(op_inner), op_inner, op_c)
    # [cfg, op_inner] |- OrdPair(c,q,inner)

    # Close
    imp1 = Implies(op_inner, op_c)
    p2 = Proof(Sequent([cfg], [imp1]), 'implies_right', [p1], principal=imp1)
    imp2 = Implies(cfg, imp1)
    p3 = Proof(Sequent([], [imp2]), 'implies_right', [p2], principal=imp2)

    proof = p3
    for v in [inner, tape, h, q, c]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], principal=fa, term=v)

    proof.name = 'config_elim'
    return proof




def transition_apply():
    """TMTransition elimination: instantiate with concrete inp pair.
    |- forall delta, q, r, w, d, qn, inp.
         TMTransition(delta,q,r,w,d,qn) -> OrdPair(inp,q,r) ->
         forall dp. OrdPair(dp,d,qn) -> forall out. OrdPair(out,w,dp) -> Apply(delta,inp,out)"""
    from core.proof import Proof, Sequent, same
    from tactics import fl, mp, ax

    delta, q, r, w, d, qn, inp = Var(), Var(), Var(), Var(), Var(), Var(), Var()
    dp, out = Var(), Var()

    trans = TMTransition(delta, q, r, w, d, qn)
    op_inp = OrdPair(inp, q, r)
    inner = Forall(dp, Implies(OrdPair(dp, d, qn),
        Forall(out, Implies(OrdPair(out, w, dp), Apply(delta, inp, out)))))

    # fl: [trans] |- OrdPair(inp,q,r) -> inner
    target = Implies(op_inp, inner)
    p0 = fl(trans, target, inp)

    # mp: [trans, op_inp] |- inner
    p1 = mp(p0, ax(op_inp), op_inp, inner)

    # Close with implies_right then foralls
    imp1 = Implies(op_inp, inner)
    p2 = Proof(Sequent([trans], [imp1]), 'implies_right', [p1], principal=imp1)
    imp2 = Implies(trans, imp1)
    p3 = Proof(Sequent([], [imp2]), 'implies_right', [p2], principal=imp2)

    proof = p3
    for v in [inp, qn, d, w, r, q, delta]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], principal=fa, term=v)

    proof.name = 'transition_apply'
    return proof




def head_move_right():
    """Moving right: Num(d,1) + Successor(h',h) -> HeadMove(h,h',d).
    |- forall h, h', d. Num(d,1) -> Successor(h',h) -> HeadMove(h,h',d)

    HeadMove(h,h',d) = Or(And(Num(d,1),Succ(h',h)), And(Num(d,0),Succ(h,h')))
    Or(A,B) = Implies(Not(A), B). We prove the left disjunct."""
    from core.proof import Proof, Sequent, same
    from vocab.tm import HeadMove
    from tactics import ax, wl
    h, hn, d = Var(), Var(), Var()

    num_d = Num(d, 1)
    succ = Successor(hn, h)
    left_and = And(num_d, succ)
    right_and = And(Num(d, 0), Successor(h, hn))
    or_form = Implies(Not(left_and), right_and)  # Or(A,B) = Implies(Not(A), B)

    # Step 1: [num_d, succ] |- left_and
    # And(A,B) = Not(Implies(A, Not(B)))
    # not_right: [num_d, succ] |- Not(Implies(num_d, Not(succ)))
    #   premise: [num_d, succ, Implies(num_d, Not(succ))] |- []
    #   implies_left on Implies(num_d, Not(succ)):
    #     branch1: [num_d, succ] |- num_d  (axiom + weaken)
    #     branch2: [num_d, succ, Not(succ)] |- []
    #       not_left on Not(succ): premise [num_d, succ] |- succ (axiom + weaken)

    b2_premise = Proof(Sequent([num_d, succ], [succ]), 'axiom', principal=succ)
    b2 = Proof(Sequent([num_d, succ, Not(succ)], []), 'not_left',
        [b2_premise], principal=Not(succ))

    b1 = wl(ax(num_d), succ)  # [num_d, succ] |- num_d

    imp_inner = Implies(num_d, Not(succ))
    il = Proof(Sequent([num_d, succ, imp_inner], []), 'implies_left',
        [b1, b2], principal=imp_inner)

    p_and = Proof(Sequent([num_d, succ], [left_and]), 'not_right',
        [il], principal=left_and)

    # Step 2: [num_d, succ] |- Or(left_and, right_and)
    # Or = Implies(Not(left_and), right_and)
    # implies_right: premise [num_d, succ, Not(left_and)] |- right_and
    # not_left on Not(left_and): premise [num_d, succ] |- right_and, left_and
    p_with_and = Proof(Sequent([num_d, succ], [right_and, left_and]), 'weakening_right',
        [p_and], principal=right_and)
    p_not_left = Proof(Sequent([num_d, succ, Not(left_and)], [right_and]), 'not_left',
        [p_with_and], principal=Not(left_and))
    p_or = Proof(Sequent([num_d, succ], [or_form]), 'implies_right',
        [p_not_left], principal=or_form)

    # Close
    imp1 = Implies(succ, or_form)
    p1 = Proof(Sequent([num_d], [imp1]), 'implies_right', [p_or], principal=imp1)
    imp2 = Implies(num_d, imp1)
    p2 = Proof(Sequent([], [imp2]), 'implies_right', [p1], principal=imp2)

    proof = p2
    for v in [d, hn, h]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], principal=fa, term=v)

    proof.name = 'head_move_right'
    return proof




def head_move_left():
    """Moving left: Num(d,0) + Successor(h,h') -> HeadMove(h,h',d).
    |- forall h, h', d. Num(d,0) -> Successor(h,h') -> HeadMove(h,h',d)

    HeadMove = Or(And(Num(d,1),Succ(h',h)), And(Num(d,0),Succ(h,h')))
    We prove the right disjunct."""
    from core.proof import Proof, Sequent, same
    from vocab.tm import HeadMove
    from tactics import ax, wl
    h, hn, d = Var(), Var(), Var()

    num_d = Num(d, 0)
    succ = Successor(h, hn)  # h = S(h') i.e. h' is predecessor
    left_and = And(Num(d, 1), Successor(hn, h))
    right_and = And(num_d, succ)
    or_form = Implies(Not(left_and), right_and)  # Or(A,B) = Implies(Not(A), B)

    # [num_d, succ] |- right_and
    # And(A,B) = Not(Implies(A, Not(B)))
    b2_premise = Proof(Sequent([num_d, succ], [succ]), 'axiom', principal=succ)
    b2 = Proof(Sequent([num_d, succ, Not(succ)], []), 'not_left',
        [b2_premise], principal=Not(succ))
    b1 = wl(ax(num_d), succ)
    imp_inner = Implies(num_d, Not(succ))
    il = Proof(Sequent([num_d, succ, imp_inner], []), 'implies_left',
        [b1, b2], principal=imp_inner)
    p_and = Proof(Sequent([num_d, succ], [right_and]), 'not_right',
        [il], principal=right_and)

    # [num_d, succ] |- Or(left_and, right_and) = Implies(Not(left_and), right_and)
    # implies_right: premise [num_d, succ, Not(left_and)] |- right_and
    # weaken_left Not(left_and) onto p_and
    p_or = Proof(Sequent([num_d, succ], [or_form]), 'implies_right',
        [wl(p_and, Not(left_and))], principal=or_form)

    # Close
    imp1 = Implies(succ, or_form)
    p1 = Proof(Sequent([num_d], [imp1]), 'implies_right', [p_or], principal=imp1)
    imp2 = Implies(num_d, imp1)
    p2 = Proof(Sequent([], [imp2]), 'implies_right', [p1], principal=imp2)

    proof = p2
    for v in [d, hn, h]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent([], [fa]), 'forall_right', [proof], principal=fa, term=v)

    proof.name = 'head_move_left'
    return proof





def step_elim():
    """TMStep elimination: from TMStep and all premises, get TMConfig(c2,...).
    |- forall delta, c1, c2, q, h, tape, sym, w, d, qn, hn, tapen.
         TMStep(delta,c1,c2) ->
         TMConfig(c1,q,h,tape) -> Apply(tape,h,sym) ->
         TMTransition(delta,q,sym,w,d,qn) ->
         TapeUpdate(tapen,tape,h,w) -> HeadMove(h,hn,d) ->
         TMConfig(c2,qn,hn,tapen)"""
    from core.proof import Proof, Sequent, same
    from tactics import apply_thm, mp, ax

    delta, c1, c2 = Var(), Var(), Var()
    q, h, tape, sym = Var(), Var(), Var(), Var()
    w, d, qn, hn, tapen = Var(), Var(), Var(), Var(), Var()

    step = TMStep(delta, c1, c2)
    cfg1 = TMConfig(c1, q, h, tape)
    app_read = Apply(tape, h, sym)
    trans = TMTransition(delta, q, sym, w, d, qn)
    tupd = TapeUpdate(tapen, tape, h, w)
    hmov = HeadMove(h, hn, d)
    cfg2 = TMConfig(c2, qn, hn, tapen)

    # TMStep has 9 foralls. Instantiate with [q,h,tape,sym,w,d,qn,hn,tapen].
    # After instantiation: cfg1 -> app -> trans -> tupd -> hmov -> cfg2
    # Then mp through 5 premises.
    imp_chain = Implies(cfg1, Implies(app_read, Implies(trans,
        Implies(tupd, Implies(hmov, cfg2)))))

    p = apply_thm(ax(step), [q, h, tape, sym, w, d, qn, hn, tapen],
        cfg1, Implies(app_read, Implies(trans, Implies(tupd, Implies(hmov, cfg2)))),
        ax(cfg1))
    p = mp(p, ax(app_read), app_read, Implies(trans, Implies(tupd, Implies(hmov, cfg2))))
    p = mp(p, ax(trans), trans, Implies(tupd, Implies(hmov, cfg2)))
    p = mp(p, ax(tupd), tupd, Implies(hmov, cfg2))
    p = mp(p, ax(hmov), hmov, cfg2)

    # p: [step, cfg1, app, trans, tupd, hmov] |- cfg2
    # Close with implies_right + forall_right
    for premise in [hmov, tupd, trans, app_read, cfg1, step]:
        imp = Implies(premise, p.sequent.right[0])
        left = [f for f in p.sequent.left if not same(f, premise)]
        p = Proof(Sequent(left, [imp]), 'implies_right', [p], principal=imp)

    for v in [tapen, hn, qn, d, w, sym, tape, h, q, c2, c1, delta]:
        body = p.sequent.right[0]
        fa = Forall(v, body)
        p = Proof(Sequent(p.sequent.left, [fa]), 'forall_right', [p], principal=fa, term=v)

    p.name = 'step_elim'
    return p




def zero_neq_one():
    """Empty and Successor are incompatible.
    |- ∀x,y,z. Empty(x) → Successor(y,z) → Not(Eq(x,y))

    Successor(y,z): ∀v. In(v,y) ↔ Or(In(v,z), Eq(v,z)). Instantiate v=z:
    In(z,y) ↔ Or(In(z,z), Eq(z,z)). Eq(z,z) true → In(z,y).
    Eq(x,y) + Empty(x) = ∀v.¬In(v,x) → ¬In(z,x). But Eq(x,y) → In(z,x)↔In(z,y).
    So In(z,x) from In(z,y). Contradiction with ¬In(z,x)."""
    from core.proof import Proof, Sequent, same
    from tactics import apply_thm, mp, ax, fl, wl
    from theorems.logic import eq_reflexive, eq_substitution, iff_mp_rev, or_intro_right
    from core.proof import Proof, Sequent

    x, y, z = Var(postfix='zx'), Var(postfix='zy'), Var(postfix='zz')
    empty_x = Empty(x)
    succ_yz = Successor(y, z)
    eq_xy = Eq(x, y)

    # Step 1: From Successor(y,z), get In(z,y).
    # Successor(y,z) = ∀v. In(v,y) ↔ Or(In(v,z), Eq(v,z))
    # Instantiate v=z: In(z,y) ↔ Or(In(z,z), Eq(z,z))
    in_zy = In(z, y)
    or_form = Or(In(z, z), Eq(z, z))
    iff_succ = Iff(in_zy, or_form)
    got_iff = apply_thm(ax(succ_yz), [z], concl=iff_succ)
    # [succ_yz] |- Iff(In(z,y), Or(In(z,z),Eq(z,z)))

    # Iff reverse: Or → In(z,y)
    got_imp_rev = apply_thm(iff_mp_rev(in_zy, or_form, []), [],
        iff_succ, Implies(or_form, in_zy), got_iff)

    # Build Or(In(z,z), Eq(z,z)) via right disjunct Eq(z,z)
    er = eq_reflexive()
    eq_zz = Eq(z, z)
    got_eq_zz = apply_thm(er, [z], concl=eq_zz)
    oil = or_intro_right(In(z, z), eq_zz, [])
    got_or = apply_thm(oil, [], eq_zz, or_form, got_eq_zz)

    got_in_zy = mp(got_imp_rev, got_or, or_form, in_zy)
    # [succ_yz] |- In(z, y)

    # Step 2: From Eq(x,y), transfer In(z,y) to In(z,x).
    # Eq(x,y) = ∀v. Iff(In(v,x), In(v,y)). Instantiate v=z:
    in_zx = In(z, x)
    iff_in = Iff(in_zx, in_zy)
    got_iff_in = apply_thm(ax(eq_xy), [z], concl=iff_in)
    # [Eq(x,y)] |- Iff(In(z,x), In(z,y))

    # Iff reverse: In(z,y) → In(z,x)
    got_imp_back = apply_thm(iff_mp_rev(in_zx, in_zy, []), [],
        iff_in, Implies(in_zy, in_zx), got_iff_in)
    got_in_zx = mp(got_imp_back, got_in_zy, in_zy, in_zx)
    # [Eq(x,y), succ_yz] |- In(z, x)

    # Step 3: From Empty(x), get ¬In(z,x).
    not_in_zx = Not(in_zx)
    got_not_in = fl(empty_x, not_in_zx, z)
    # [Empty(x)] |- ¬In(z, x)

    # Contradiction: build [Eq(x,y), succ_yz, Empty(x)] |- [] via not_left + cut
    got_in_zx_w = wl(got_in_zx, empty_x)
    # [Eq(x,y), succ_yz, Empty(x)] |- In(z,x)
    got_not_in_w = wl(got_not_in, eq_xy, succ_yz)
    # [Empty(x), Eq(x,y), succ_yz] |- ¬In(z,x)

    # not_left: [ctx, ¬In(z,x)] |- [] from [ctx] |- [In(z,x)]
    ctx_all = list(got_in_zx_w.sequent.left)
    got_bot_nl = Proof(Sequent(ctx_all + [not_in_zx], []),
        'not_left', [got_in_zx_w], principal=not_in_zx)
    # [Eq(x,y), succ_yz, Empty(x), ¬In(z,x)] |- []

    # cut ¬In(z,x): ps0 = [G] |- [¬In(z,x)], ps1 = [G, ¬In(z,x)] |- []
    from tactics import weaken_to
    ps0 = weaken_to(got_not_in_w, ctx_all)
    got_bot = Proof(Sequent(ctx_all, []), 'cut',
        [ps0, got_bot_nl], principal=not_in_zx)
    # [Eq(x,y), succ_yz, Empty(x)] |- []

    # not_right on Eq(x,y): [succ_yz, Empty(x)] |- Not(Eq(x,y))
    not_eq = Not(eq_xy)
    got_not_eq = Proof(Sequent([f for f in got_bot.sequent.left if not same(f, eq_xy)],
        [not_eq]), 'not_right', [got_bot], principal=not_eq)

    # Close: implies_right + forall_right
    for premise in [succ_yz, empty_x]:
        imp = Implies(premise, got_not_eq.sequent.right[0])
        left = [f for f in got_not_eq.sequent.left if not same(f, premise)]
        got_not_eq = Proof(Sequent(left, [imp]), 'implies_right', [got_not_eq], principal=imp)

    proof = got_not_eq
    for v in [z, y, x]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'zero_neq_one'
    return proof




def tape_update_eq():
    """Identity tape update: writing the same value gives the same tape.
    Extensionality, Pairing |- forall tapen, tape, h, w.
        Function(tape) -> Apply(tape,h,w) -> TapeUpdate(tapen,tape,h,w) -> Eq(tapen, tape)

    From TapeUpdate (In-based), show ∀p. In(p,tapen) ↔ In(p,tape), then Extensionality.
    Forward: In(p,tapen) → Or(OrdPair(p,h,w), And(In(p,tape),...)) → In(p,tape).
      Left: OrdPair(p,h,w) + Apply(tape,h,w) → ordpair_unique → In(p,tape).
      Right: In(p,tape) directly.
    Backward: In(p,tape) → Or(OrdPair(p,h,w), And(In(p,tape),¬∃y.OrdPair(p,h,y))).
      Or = Implies(Not(left), right). Assume ¬OrdPair(p,h,w). Prove ¬∃y.OrdPair(p,h,y):
      Assume OrdPair(p,h,y). From In(p,tape)+OrdPair(p,h,y) → Apply(tape,h,y).
      func_unique + Apply(tape,h,w) → Eq(y,w). Transfer → OrdPair(p,h,w). Contradiction."""
    from core.proof import Proof, Sequent, same
    from tactics import apply_thm, mp, ax, wl, wr, fl, eir, eel, cut
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_intro, iff_mp, iff_mp_rev, or_elim, eq_substitution)
    from theorems.sets import ordpair_exists, ordpair_unique, ordpair_val_transfer
    from vocab.functions import Function as FuncDef
    from core.proof import Proof, Sequent

    tapen, tape, h, w = Var(postfix='tn'), Var(postfix='tp'), Var(postfix='hd'), Var(postfix='wr')
    p = Var(postfix='ep')
    yv = Var(postfix='ey')
    tu = TapeUpdate(tapen, tape, h, w)
    func_tape = FuncDef(tape)
    app_hw = Apply(tape, h, w)

    # TapeUpdate expanded components
    in_p_tn = In(p, tapen)
    in_p_tp = In(p, tape)
    op_phw = OrdPair(p, h, w)
    op_phy = OrdPair(p, h, yv)
    not_ex_y = Not(Exists(yv, op_phy))
    right_and = And(in_p_tp, not_ex_y)
    or_form = Or(op_phw, right_and)
    iff_tu = Iff(in_p_tn, or_form)

    # === Forward: In(p, tapen) → In(p, tape) ===

    # Step F1: [tu] |- Iff(In(p,tapen), Or(...))
    got_iff = apply_thm(ax(tu), [p], concl=iff_tu)

    # Step F2: Iff forward → In(p,tapen) → Or(...)
    iff_fwd = iff_mp(in_p_tn, or_form, [])
    got_fwd = apply_thm(iff_fwd, [], iff_tu, Implies(in_p_tn, or_form), got_iff)
    # [tu] |- In(p,tapen) → Or(...)

    # Step F3: Or-elim. Left case: OrdPair(p,h,w) → In(p,tape).
    # From Apply(tape,h,w) = ∃q. OrdPair(q,h,w) ∧ In(q,tape).
    # OrdPair(p,h,w) ∧ OrdPair(q,h,w) → Eq(p,q) → In(p,tape).

    q = Var(postfix='eq')
    op_qhw = OrdPair(q, h, w)
    in_q_tp = In(q, tape)
    and_q = And(op_qhw, in_q_tp)

    # ordpair_unique: Pairing |- ∀a,b,t,s. OrdPair(t,a,b) → OrdPair(s,a,b) → Eq(t,s)
    ou = ordpair_unique()
    eq_pq = Eq(p, q)
    got_eq_pq = mp(apply_thm(ou, [h, w, p, q], op_phw,
        Implies(op_qhw, eq_pq), ax(op_phw)),
        ax(op_qhw), op_qhw, eq_pq)
    # [Pairing, OrdPair(p,h,w), OrdPair(q,h,w)] |- Eq(p,q)

    # eq_substitution: Eq(p,q) → Iff(In(p,tape), In(q,tape))
    from theorems.logic import eq_substitution
    es = eq_substitution()
    iff_in = Iff(In(p, tape), In(q, tape))
    got_iff_in = apply_thm(es, [p, q, tape], eq_pq, iff_in, got_eq_pq)
    # [..., OrdPair(p,h,w), OrdPair(q,h,w)] |- Iff(In(p,tape), In(q,tape))

    # Iff reverse: In(q,tape) → In(p,tape)
    iff_rev_in = iff_mp_rev(In(p, tape), In(q, tape), [])
    got_imp_in = apply_thm(iff_rev_in, [], iff_in,
        Implies(in_q_tp, in_p_tp), got_iff_in)
    got_in_from_q = mp(got_imp_in, ax(in_q_tp), in_q_tp, in_p_tp)
    # [..., OrdPair(p,h,w), OrdPair(q,h,w), In(q,tape)] |- In(p,tape)

    # Combine OrdPair(q,h,w) and In(q,tape) from And(op_qhw, in_q_tp):
    ael_q = and_elim_left(op_qhw, in_q_tp, [])
    aer_q = and_elim_right(op_qhw, in_q_tp, [])
    got_opq_from_and = apply_thm(ael_q, [], and_q, op_qhw, ax(and_q))
    got_inq_from_and = apply_thm(aer_q, [], and_q, in_q_tp, ax(and_q))
    got_in_left = cut(got_in_from_q, op_qhw, got_opq_from_and)
    got_in_left = cut(got_in_left, in_q_tp, got_inq_from_and)
    # [..., OrdPair(p,h,w), And(op_qhw, in_q_tp)] |- In(p,tape)

    # eel q from And(op_qhw, in_q_tp) → Exists(q, And(...)) = Apply(tape,h,w)
    got_in_left = eel(got_in_left, and_q, q)
    # [..., OrdPair(p,h,w), Apply(tape,h,w)] |- In(p,tape)

    # Step F4: Right case: And(In(p,tape), ¬∃y.OrdPair(p,h,y)) → In(p,tape)
    ael_r = and_elim_left(in_p_tp, not_ex_y, [])
    got_in_right = apply_thm(ael_r, [], right_and, in_p_tp, ax(right_and))
    # [right_and] |- In(p, tape)

    # Step F5: Or-elim: Or(A,B) → (A→C) → (B→C) → C
    oe = or_elim(op_phw, right_and, in_p_tp, [])
    # or_elim: |- Or(A,B) → (A→C) → (B→C) → C

    # Build A → C and B → C
    imp_ac = Implies(op_phw, in_p_tp)
    left_no_op = [f for f in got_in_left.sequent.left if not same(f, op_phw)]
    got_imp_ac = Proof(Sequent(left_no_op, [imp_ac]),
        'implies_right', [got_in_left], principal=imp_ac)

    imp_bc = Implies(right_and, in_p_tp)
    got_imp_bc = Proof(Sequent([], [imp_bc]),
        'implies_right', [got_in_right], principal=imp_bc)

    # mp chain: Or → (A→C) → (B→C) → C
    # First get Or from fwd: In(p,tapen) → Or
    got_fwd_final = mp(got_fwd, ax(in_p_tn), in_p_tn, or_form)
    # [tu, In(p,tapen)] |- Or(...)

    got_oe = apply_thm(oe, [], or_form,
        Implies(imp_ac, Implies(imp_bc, in_p_tp)), got_fwd_final)
    got_oe = mp(got_oe, got_imp_ac, imp_ac, Implies(imp_bc, in_p_tp))
    got_oe = mp(got_oe, got_imp_bc, imp_bc, in_p_tp)
    got_fwd_result = got_oe
    # [tu, In(p,tapen), Apply(tape,h,w), Pairing] |- In(p,tape)

    # === Backward: In(p, tape) → In(p, tapen) ===

    # Or = Implies(Not(left), right). So Or(op_phw, right_and) = Implies(Not(op_phw), right_and).
    # Assume Not(OrdPair(p,h,w)). Prove And(In(p,tape), ¬∃y.OrdPair(p,h,y)).
    # In(p,tape) we have.
    # ¬∃y.OrdPair(p,h,y): assume OrdPair(p,h,yv).
    #   From In(p,tape) + OrdPair(p,h,yv): Apply(tape,h,yv) (eir with witness p).
    #   func_unique + Apply(tape,h,w) → Eq(yv,w).
    #   ordpair_val_transfer + OrdPair(p,h,yv) + Eq(yv,w) → OrdPair(p,h,w).
    #   Contradicts Not(OrdPair(p,h,w)).

    # Build Apply(tape,h,yv) from OrdPair(p,h,yv) + In(p,tape):
    ai_app = and_intro(op_phy, in_p_tp, [])
    got_and_app = mp(apply_thm(ai_app, [], op_phy,
        Implies(in_p_tp, And(op_phy, in_p_tp)), ax(op_phy)),
        ax(in_p_tp), in_p_tp, And(op_phy, in_p_tp))
    got_app_hy = eir(got_and_app, And(op_phy, in_p_tp), p, p)
    # [OrdPair(p,h,yv), In(p,tape)] |- Apply(tape, h, yv)

    # func_unique: Function(tape) → Apply(tape,h,yv) → Apply(tape,h,w) → Eq(yv,w)
    from theorems.omega import func_unique_thm
    fu = func_unique_thm()
    eq_yw = Eq(yv, w)
    got_fu = apply_thm(fu, [tape, h, yv, w])
    got_fu = mp(got_fu, ax(func_tape), func_tape, got_fu.sequent.right[0].right)
    got_fu = mp(got_fu, got_app_hy, Apply(tape, h, yv), got_fu.sequent.right[0].right)
    got_fu = mp(got_fu, ax(app_hw), app_hw, eq_yw)
    # [Function(tape), OrdPair(p,h,yv), In(p,tape), Apply(tape,h,w)] |- Eq(yv, w)

    # ordpair_val_transfer: Eq(b,c) → OrdPair(t,a,b) → OrdPair(t,a,c)
    from theorems.sets import ordpair_val_transfer
    ovt = ordpair_val_transfer()
    got_ophw2 = mp(apply_thm(ovt, [p, h, yv, w], eq_yw,
        Implies(op_phy, op_phw), got_fu),
        ax(op_phy), op_phy, op_phw)
    # [..., OrdPair(p,h,yv), In(p,tape)] |- OrdPair(p,h,w)

    # Contradiction with Not(OrdPair(p,h,w)):
    not_ophw = Not(op_phw)
    got_bot = Proof(Sequent(list(got_ophw2.sequent.left) + [not_ophw], []),
        'not_left', [got_ophw2], principal=not_ophw)

    # not_right on OrdPair(p,h,yv) → ¬OrdPair(p,h,yv)
    not_ophy = Not(op_phy)
    got_not_ophy = Proof(Sequent([f for f in got_bot.sequent.left if not same(f, op_phy)],
        [not_ophy]), 'not_right', [got_bot], principal=not_ophy)

    # forall_right yv → ∀yv. ¬OrdPair(p,h,yv) then convert to ¬∃yv.OrdPair(p,h,yv)
    fa_not_ophy = Forall(yv, not_ophy)
    got_fa_not = Proof(Sequent(got_not_ophy.sequent.left, [fa_not_ophy]),
        'forall_right', [got_not_ophy], principal=fa_not_ophy, term=yv)
    # Convert: ∀yv.¬P → ¬∃yv.P
    ex_phy = Exists(yv, op_phy)
    got_bot3 = Proof(Sequent(list(got_fa_not.sequent.left) + [ex_phy], []),
        'not_left', [got_fa_not], principal=ex_phy)
    got_not_ex = Proof(Sequent([f for f in got_bot3.sequent.left if not same(f, ex_phy)],
        [not_ex_y]), 'not_right', [got_bot3], principal=not_ex_y)
    # [Function(tape), In(p,tape), Apply(tape,h,w), Not(OrdPair(p,h,w))] |- ¬∃yv.OrdPair(p,h,yv)

    # And(In(p,tape), not_ex_y)
    ai_back = and_intro(in_p_tp, not_ex_y, [])
    got_back_and = mp(apply_thm(ai_back, [], in_p_tp,
        Implies(not_ex_y, right_and), ax(in_p_tp)),
        got_not_ex, not_ex_y, right_and)
    # [..., In(p,tape), Not(OrdPair(p,h,w))] |- And(In(p,tape), ¬∃yv.OrdPair(p,h,yv))

    # This IS Or(OrdPair(p,h,w), right_and) via implies_right on Not(OrdPair(p,h,w))
    # Or(A,B) = Implies(Not(A), B)
    got_or_back = Proof(Sequent(
        [f for f in got_back_and.sequent.left if not same(f, not_ophw)],
        [or_form]), 'implies_right', [got_back_and], principal=or_form)
    # [Function(tape), In(p,tape), Apply(tape,h,w)] |- Or(OrdPair(p,h,w), right_and)

    # Iff reverse: Or → In(p,tapen)
    got_iff2 = apply_thm(ax(tu), [p], concl=iff_tu)
    iff_rev2 = iff_mp_rev(in_p_tn, or_form, [])
    got_imp_rev = apply_thm(iff_rev2, [], iff_tu,
        Implies(or_form, in_p_tn), got_iff2)
    got_back_result = mp(got_imp_rev, got_or_back, or_form, in_p_tn)
    # [tu, Function(tape), In(p,tape), Apply(tape,h,w)] |- In(p,tapen)

    # === Iff: In(p,tape) ↔ In(p,tapen) then Extensionality → Eq(tapen, tape) ===

    # Build Iff(In(p,tapen), In(p,tape)):
    # Forward: [ctx, In(p,tapen)] |- In(p,tape)
    # Backward: [ctx, In(p,tape)] |- In(p,tapen)
    ii = iff_intro(in_p_tn, in_p_tp, [])
    # iff_intro: (A→B) → (B→A) → Iff(A,B)
    imp_fwd = Implies(in_p_tn, in_p_tp)
    fwd_left = [f for f in got_fwd_result.sequent.left if not same(f, in_p_tn)]
    got_imp_fwd = Proof(Sequent(fwd_left, [imp_fwd]),
        'implies_right', [got_fwd_result], principal=imp_fwd)
    imp_back = Implies(in_p_tp, in_p_tn)
    back_left = [f for f in got_back_result.sequent.left if not same(f, in_p_tp)]
    got_imp_back = Proof(Sequent(back_left, [imp_back]),
        'implies_right', [got_back_result], principal=imp_back)

    iff_ptn_ptp = Iff(in_p_tn, in_p_tp)
    got_iff_final = mp(apply_thm(ii, [], imp_fwd,
        Implies(imp_back, iff_ptn_ptp), got_imp_fwd),
        got_imp_back, imp_back, iff_ptn_ptp)
    # [tu, Apply(tape,h,w), Pairing, Function(tape)] |- Iff(In(p,tapen), In(p,tape))

    # forall_right on p
    fa_iff = Forall(p, iff_ptn_ptp)
    got_fa_iff = Proof(Sequent(got_iff_final.sequent.left, [fa_iff]),
        'forall_right', [got_iff_final], principal=fa_iff, term=p)
    # [...] |- ∀p. Iff(In(p,tapen), In(p,tape))

    # ∀p. In(p,tapen) ↔ In(p,tape) IS Eq(tapen,tape) by definition (extensional equality).
    # No Extensionality axiom needed!
    got_eq = got_fa_iff
    # [tu, Apply(tape,h,w), Pairing, Function(tape)] |- Eq(tapen, tape)

    # Close: implies_right for tu, app_hw, func_tape; forall_right for tapen, tape, h, w
    for premise in [tu, app_hw, func_tape]:
        imp = Implies(premise, got_eq.sequent.right[0])
        left = [f for f in got_eq.sequent.left if not same(f, premise)]
        got_eq = Proof(Sequent(left, [imp]), 'implies_right', [got_eq], principal=imp)

    proof = got_eq
    for v in [w, h, tape, tapen]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'tape_update_eq'
    return proof




def config_eq():
    """Two TMConfigs of the same set imply component equality.
    |- forall c, q1, h1, t1, q2, h2, t2.
         TMConfig(c,q1,h1,t1) -> TMConfig(c,q2,h2,t2) ->
         And(Eq(q1,q2), And(Eq(h1,h2), Eq(t1,t2)))

    Uses ordpair_set_transfer + tuple_injection twice."""
    from core.proof import Proof, Sequent, same
    from tactics import apply_thm, mp, ax, eel, cut
    from theorems.logic import and_elim_left, and_elim_right, and_intro
    from theorems.sets import ordpair_set_transfer
    import theorems

    c = Var(postfix='c')
    q1, h1, t1 = Var(postfix='q1'), Var(postfix='h1'), Var(postfix='t1')
    q2, h2, t2 = Var(postfix='q2'), Var(postfix='h2'), Var(postfix='t2')
    inner1, inner2 = Var(postfix='i1'), Var(postfix='i2')

    cfg1 = TMConfig(c, q1, h1, t1)
    cfg2 = TMConfig(c, q2, h2, t2)
    ce = config_elim()
    ti = theorems.tuple_injection()
    oe = theorems.ordpair_exists()
    ost = ordpair_set_transfer()

    op1 = OrdPair(inner1, h1, t1)
    op2 = OrdPair(inner2, h2, t2)

    # Witnesses: exists inner1. OrdPair(inner1,h1,t1), exists inner2. OrdPair(inner2,h2,t2)
    got_ex1 = apply_thm(oe, [h1, t1], concl=Exists(inner1, op1))
    got_ex2 = apply_thm(oe, [h2, t2], concl=Exists(inner2, op2))

    # config_elim: cfg + OrdPair -> OrdPair(c,q,inner)
    oc1 = OrdPair(c, q1, inner1)
    got_oc1 = mp(apply_thm(ce, [c,q1,h1,t1,inner1], cfg1, Implies(op1,oc1), ax(cfg1)),
        ax(op1), op1, oc1)
    oc2 = OrdPair(c, q2, inner2)
    got_oc2 = mp(apply_thm(ce, [c,q2,h2,t2,inner2], cfg2, Implies(op2,oc2), ax(cfg2)),
        ax(op2), op2, oc2)

    # tuple_injection outer: Eq(q1,q2), Eq(inner1,inner2)
    eq_q = Eq(q1, q2)
    eq_ii = Eq(inner1, inner2)
    and_outer = And(eq_q, eq_ii)
    got_outer = mp(apply_thm(ti, [q1,inner1,q2,inner2,c], oc1,
        Implies(oc2, and_outer), got_oc1), got_oc2, oc2, and_outer)
    got_eq_q = apply_thm(and_elim_left(eq_q, eq_ii, []), [], and_outer, eq_q, got_outer)
    got_eq_ii = apply_thm(and_elim_right(eq_q, eq_ii, []), [], and_outer, eq_ii, got_outer)

    # ordpair_set_transfer: Eq(inner1,inner2) + OrdPair(inner2,h2,t2) -> OrdPair(inner1,h2,t2)
    op1_h2t2 = OrdPair(inner1, h2, t2)
    got_op1_h2t2 = mp(apply_thm(ost, [inner1,inner2,h2,t2], eq_ii,
        Implies(op2, op1_h2t2), got_eq_ii), ax(op2), op2, op1_h2t2)

    # tuple_injection inner: Eq(h1,h2), Eq(t1,t2)
    eq_h = Eq(h1, h2)
    eq_t = Eq(t1, t2)
    and_inner = And(eq_h, eq_t)
    got_inner = mp(apply_thm(ti, [h1,t1,h2,t2,inner1], op1,
        Implies(op1_h2t2, and_inner), ax(op1)),
        got_op1_h2t2, op1_h2t2, and_inner)
    got_eq_h = apply_thm(and_elim_left(eq_h, eq_t, []), [], and_inner, eq_h, got_inner)
    got_eq_t = apply_thm(and_elim_right(eq_h, eq_t, []), [], and_inner, eq_t, got_inner)

    # Assemble: And(Eq(q1,q2), And(Eq(h1,h2), Eq(t1,t2)))
    ht_and = And(eq_h, eq_t)
    got_ht = mp(apply_thm(and_intro(eq_h, eq_t, []), [], eq_h,
        Implies(eq_t, ht_and), got_eq_h), got_eq_t, eq_t, ht_and)
    result = And(eq_q, ht_and)
    got_result = mp(apply_thm(and_intro(eq_q, ht_and, []), [], eq_q,
        Implies(ht_and, result), got_eq_q), got_ht, ht_and, result)

    # Eliminate existential witnesses
    got_result = eel(got_result, op1, inner1)
    got_result = cut(got_result, got_result.sequent.left[-1], got_ex1)
    got_result = eel(got_result, op2, inner2)
    got_result = cut(got_result, got_result.sequent.left[-1], got_ex2)

    # Close
    for premise in [cfg2, cfg1]:
        imp = Implies(premise, got_result.sequent.right[0])
        left = [f for f in got_result.sequent.left if not same(f, premise)]
        got_result = Proof(Sequent(left, [imp]), 'implies_right', [got_result], principal=imp)

    proof = got_result
    for v in [t2, h2, q2, t1, h1, q1, c]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'config_eq'
    return proof




def config_eq_transfer():
    """Transfer TMConfig across Eq's on components.
    Pairing |- ∀c,q1,h1,t1,q2,h2,t2.
        TMConfig(c,q1,h1,t1) → Eq(q1,q2) → Eq(h1,h2) → Eq(t1,t2) →
        TMConfig(c,q2,h2,t2)

    Strategy: TMConfig(c,q2,h2,t2) = ∀v. OrdPair(v,h2,t2) → OrdPair(c,q2,v).
    From TMConfig(c,q1,h1,t1) with inner pair + Eq transfers + config_intro."""
    from core.proof import Proof, Sequent, same
    from tactics import apply_thm, mp, ax, wl, eir, eel, cut
    from theorems.logic import (and_elim_left, and_elim_right, eq_symmetric,
        iff_chain, iff_mp, iff_mp_rev, iff_sym, eq_substitution)
    from theorems.sets import eq_in_eq, ordpair_exists
    from theorems.logic import or_iff_compat
    from theorems.tm import config_intro
    from core.proof import Proof, Sequent
    from core.derived import Exists

    c = Var(postfix='ec')
    q1, h1, t1 = Var(postfix='eq1'), Var(postfix='eh1'), Var(postfix='et1')
    q2, h2, t2 = Var(postfix='eq2'), Var(postfix='eh2'), Var(postfix='et2')

    cfg1 = TMConfig(c, q1, h1, t1)
    cfg2 = TMConfig(c, q2, h2, t2)
    eq_q = Eq(q1, q2)
    eq_h = Eq(h1, h2)
    eq_t = Eq(t1, t2)

    # Strategy: Config(c,q2,h2,t2) = ∀v. OrdPair(v,h2,t2) → OrdPair(c,q2,v).
    # From Config(c,q1,h1,t1): ∀v. OrdPair(v,h1,t1) → OrdPair(c,q1,v).
    # For a given v with OrdPair(v,h2,t2):
    #   Eq(h1,h2)+Eq(t1,t2) → OrdPair(v,h2,t2) ↔ OrdPair(v,h1,t1) (via Eq transfers on pair elements)
    #   Actually simpler: from OrdPair(v,h2,t2), use ordpair_eq_transfer backwards:
    #     Eq(h2,h1)+Eq(t2,t1) → OrdPair(v,h2,t2) → OrdPair(v,h1,t1)
    #   Then Config(c,q1,h1,t1) gives OrdPair(c,q1,v).
    #   Then Eq(q1,q2) → OrdPair(c,q2,v) via ordpair_eq_transfer.
    #   OrdPair(v,h2,t2) → OrdPair(c,q2,v) for all v = Config(c,q2,h2,t2).

    from theorems.sets import ordpair_eq_transfer
    oet = ordpair_eq_transfer()
    es = eq_symmetric()

    v = Var(postfix='ev')
    op_v_h2t2 = OrdPair(v, h2, t2)
    op_v_h1t1 = OrdPair(v, h1, t1)
    op_c_q1_v = OrdPair(c, q1, v)
    op_c_q2_v = OrdPair(c, q2, v)

    # Eq(h2,h1) and Eq(t2,t1) from symmetry
    eq_h_sym = Eq(h2, h1)
    eq_t_sym = Eq(t2, t1)
    got_eq_h_sym = apply_thm(es, [h1, h2], eq_h, eq_h_sym, ax(eq_h))
    got_eq_t_sym = apply_thm(es, [t1, t2], eq_t, eq_t_sym, ax(eq_t))

    # OrdPair(v,h2,t2) → OrdPair(v,h1,t1) via ordpair_eq_transfer(h2,t2,h1,t1,v)
    got_op_v_h1t1 = apply_thm(oet, [h2, t2, h1, t1, v])
    got_op_v_h1t1 = mp(got_op_v_h1t1, got_eq_h_sym, eq_h_sym, got_op_v_h1t1.sequent.right[0].right)
    got_op_v_h1t1 = mp(got_op_v_h1t1, got_eq_t_sym, eq_t_sym, got_op_v_h1t1.sequent.right[0].right)
    got_op_v_h1t1 = mp(got_op_v_h1t1, ax(op_v_h2t2), op_v_h2t2, op_v_h1t1)
    # [Eq(h1,h2), Eq(t1,t2), OrdPair(v,h2,t2)] |- OrdPair(v,h1,t1)

    # Config(c,q1,h1,t1) instantiated with v: OrdPair(v,h1,t1) → OrdPair(c,q1,v)
    got_cfg_inst = apply_thm(ax(cfg1), [v], op_v_h1t1, op_c_q1_v, got_op_v_h1t1)
    # [cfg1, Eq(h1,h2), Eq(t1,t2), OrdPair(v,h2,t2)] |- OrdPair(c,q1,v)

    # Eq(q1,q2) → OrdPair(c,q1,v) → OrdPair(c,q2,v)
    # ordpair_eq_transfer(q1,v,q2,v,c): Eq(q1,q2) → Eq(v,v) → OrdPair(c,q1,v) → OrdPair(c,q2,v)
    # We need Eq(v,v) too. Use eq_reflexive.
    from theorems.logic import eq_reflexive
    er = eq_reflexive()
    eq_vv = Eq(v, v)
    got_eq_vv = apply_thm(er, [v], concl=eq_vv)

    got_op_c_q2_v = apply_thm(oet, [q1, v, q2, v, c])
    got_op_c_q2_v = mp(got_op_c_q2_v, ax(eq_q), eq_q, got_op_c_q2_v.sequent.right[0].right)
    got_op_c_q2_v = mp(got_op_c_q2_v, got_eq_vv, eq_vv, got_op_c_q2_v.sequent.right[0].right)
    got_op_c_q2_v = mp(got_op_c_q2_v, got_cfg_inst, op_c_q1_v, op_c_q2_v)
    # [cfg1, Eq(q1,q2), Eq(h1,h2), Eq(t1,t2), OrdPair(v,h2,t2)] |- OrdPair(c,q2,v)

    # Close: implies_right on OrdPair(v,h2,t2), forall_right on v → TMConfig(c,q2,h2,t2)
    imp = Implies(op_v_h2t2, op_c_q2_v)
    left = [f for f in got_op_c_q2_v.sequent.left if not same(f, op_v_h2t2)]
    got_cfg2_body = Proof(Sequent(left, [imp]), 'implies_right', [got_op_c_q2_v], principal=imp)
    fa = Forall(v, imp)
    got_cfg2 = Proof(Sequent(got_cfg2_body.sequent.left, [fa]),
        'forall_right', [got_cfg2_body], principal=fa, term=v)
    # [cfg1, Eq(q1,q2), Eq(h1,h2), Eq(t1,t2)] |- TMConfig(c,q2,h2,t2)

    # Close outer implies + foralls
    for premise in [eq_t, eq_h, eq_q, cfg1]:
        imp = Implies(premise, got_cfg2.sequent.right[0])
        left = [f for f in got_cfg2.sequent.left if not same(f, premise)]
        got_cfg2 = Proof(Sequent(left, [imp]), 'implies_right', [got_cfg2], principal=imp)

    proof = got_cfg2
    for vv in [t2, h2, q2, t1, h1, q1, c]:
        body = proof.sequent.right[0]
        fa = Forall(vv, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=vv)

    proof.name = 'config_eq_transfer'
    return proof




def transition_unique():
    """Extract Eq's from two TMTransitions on the same input via Function(delta).
    Pairing |- ∀delta,q,sym,w,d,qn,w2,d2,qn2.
        Function(delta) →
        TMTransition(delta,q,sym,w,d,qn) → TMTransition(delta,q,sym,w2,d2,qn2) →
        And(Eq(w,w2), And(Eq(d,d2), Eq(qn,qn2)))

    Instantiate both with same inp pair, func_unique → Eq(out1,out2),
    tuple_injection on output structure → Eq's on (w,dp) then (d,qn)."""
    from core.proof import Proof, Sequent, same
    from tactics import apply_thm, mp, ax, wl, eir, eel, cut
    from theorems.logic import and_intro, and_elim_left, and_elim_right, eq_symmetric
    from theorems.sets import ordpair_exists, ordpair_set_transfer, tuple_injection
    from theorems.omega import func_unique_thm
    from vocab.functions import Function as FuncDef
    from core.proof import Proof, Sequent
    from core.derived import Exists

    delta = Var(postfix='td')
    q, sym = Var(postfix='tq'), Var(postfix='ts')
    w, d, qn = Var(postfix='tw'), Var(postfix='tdd'), Var(postfix='tqn')
    w2, d2, qn2 = Var(postfix='tw2'), Var(postfix='td2'), Var(postfix='tqn2')

    func_d = FuncDef(delta)
    trans1 = TMTransition(delta, q, sym, w, d, qn)
    trans2 = TMTransition(delta, q, sym, w2, d2, qn2)

    oe = ordpair_exists()
    ti = tuple_injection()
    fu = func_unique_thm()
    es = eq_symmetric()
    ost = ordpair_set_transfer()

    # Create pair witnesses
    inp = Var(postfix='tinp')
    dp1, dp2 = Var(postfix='tdp1'), Var(postfix='tdp2')
    out1, out2 = Var(postfix='to1'), Var(postfix='to2')

    op_inp = OrdPair(inp, q, sym)
    op_dp1 = OrdPair(dp1, d, qn)
    op_dp2 = OrdPair(dp2, d2, qn2)
    op_out1 = OrdPair(out1, w, dp1)
    op_out2 = OrdPair(out2, w2, dp2)

    got_ex_inp = apply_thm(oe, [q, sym], concl=Exists(inp, op_inp))
    got_ex_dp1 = apply_thm(oe, [d, qn], concl=Exists(dp1, op_dp1))
    got_ex_dp2 = apply_thm(oe, [d2, qn2], concl=Exists(dp2, op_dp2))
    got_ex_out1 = apply_thm(oe, [w, dp1], concl=Exists(out1, op_out1))
    got_ex_out2 = apply_thm(oe, [w2, dp2], concl=Exists(out2, op_out2))

    # Instantiate trans1 with inp, dp1, out1 → Apply(delta, inp, out1)
    app_d1 = Apply(delta, inp, out1)
    got_t1 = apply_thm(ax(trans1), [inp], op_inp,
        Forall(dp1, Implies(op_dp1, Forall(out1, Implies(op_out1, app_d1)))), ax(op_inp))
    got_t1 = apply_thm(got_t1, [dp1], op_dp1,
        Forall(out1, Implies(op_out1, app_d1)), ax(op_dp1))
    got_t1 = apply_thm(got_t1, [out1], op_out1, app_d1, ax(op_out1))

    # Instantiate trans2 with inp, dp2, out2 → Apply(delta, inp, out2)
    app_d2 = Apply(delta, inp, out2)
    got_t2 = apply_thm(ax(trans2), [inp], op_inp,
        Forall(dp2, Implies(op_dp2, Forall(out2, Implies(op_out2, app_d2)))), ax(op_inp))
    got_t2 = apply_thm(got_t2, [dp2], op_dp2,
        Forall(out2, Implies(op_out2, app_d2)), ax(op_dp2))
    got_t2 = apply_thm(got_t2, [out2], op_out2, app_d2, ax(op_out2))

    # func_unique: Function(delta) → Apply(delta,inp,out1) → Apply(delta,inp,out2) → Eq(out1,out2)
    eq_out = Eq(out1, out2)
    got_eq_out = apply_thm(fu, [delta, inp, out1, out2])
    got_eq_out = mp(got_eq_out, ax(func_d), func_d, got_eq_out.sequent.right[0].right)
    got_eq_out = mp(got_eq_out, got_t1, app_d1, got_eq_out.sequent.right[0].right)
    got_eq_out = mp(got_eq_out, got_t2, app_d2, eq_out)

    # tuple_injection on out1 vs out2: OrdPair(out1,w,dp1) and OrdPair(out2,w2,dp2)
    # Transfer out2→out1 via ordpair_set_transfer: Eq(s1,s2) → OrdPair(s2,..) → OrdPair(s1,..)
    # With s1=out1, s2=out2: Eq(out1,out2) → OrdPair(out2,w2,dp2) → OrdPair(out1,w2,dp2)
    op_out1_w2 = OrdPair(out1, w2, dp2)
    got_out1_w2 = mp(apply_thm(ost, [out1, out2, w2, dp2], eq_out,
        Implies(op_out2, op_out1_w2), got_eq_out),
        ax(op_out2), op_out2, op_out1_w2)

    eq_w = Eq(w, w2)
    eq_dp = Eq(dp1, dp2)
    got_ti1 = apply_thm(ti, [w, dp1, w2, dp2, out1])
    got_ti1 = mp(got_ti1, ax(op_out1), op_out1, Implies(op_out1_w2, And(eq_w, eq_dp)))
    got_ti1 = mp(got_ti1, got_out1_w2, op_out1_w2, And(eq_w, eq_dp))
    got_eq_w = apply_thm(and_elim_left(eq_w, eq_dp, []), [], And(eq_w, eq_dp), eq_w, got_ti1)
    got_eq_dp = apply_thm(and_elim_right(eq_w, eq_dp, []), [], And(eq_w, eq_dp), eq_dp, got_ti1)

    # tuple_injection on dp1 vs dp2: OrdPair(dp1,d,qn) and OrdPair(dp2,d2,qn2)
    # ordpair_set_transfer: Eq(dp1,dp2) → OrdPair(dp2,d2,qn2) → OrdPair(dp1,d2,qn2)
    op_dp1_d2 = OrdPair(dp1, d2, qn2)
    got_dp1_d2 = mp(apply_thm(ost, [dp1, dp2, d2, qn2], eq_dp,
        Implies(op_dp2, op_dp1_d2), got_eq_dp),
        ax(op_dp2), op_dp2, op_dp1_d2)

    eq_d = Eq(d, d2)
    eq_qn = Eq(qn, qn2)
    got_ti2 = apply_thm(ti, [d, qn, d2, qn2, dp1])
    got_ti2 = mp(got_ti2, ax(op_dp1), op_dp1, Implies(op_dp1_d2, And(eq_d, eq_qn)))
    got_ti2 = mp(got_ti2, got_dp1_d2, op_dp1_d2, And(eq_d, eq_qn))
    got_eq_d = apply_thm(and_elim_left(eq_d, eq_qn, []), [], And(eq_d, eq_qn), eq_d, got_ti2)
    got_eq_qn = apply_thm(and_elim_right(eq_d, eq_qn, []), [], And(eq_d, eq_qn), eq_qn, got_ti2)

    # Eliminate existential witnesses: out2, dp2, out1, dp1, inp
    def elim_var(proof, formula, var, ex_proof):
        if any(same(formula, ff) for ff in proof.sequent.left):
            p = eel(proof, formula, var)
            return cut(p, Exists(var, formula), ex_proof)
        return proof

    elim_list = [
        (out2, op_out2, got_ex_out2), (dp2, op_dp2, got_ex_dp2),
        (out1, op_out1, got_ex_out1), (dp1, op_dp1, got_ex_dp1),
        (inp, op_inp, got_ex_inp)]
    for var, formula, ex_p in elim_list:
        got_eq_w = elim_var(got_eq_w, formula, var, ex_p)
        got_eq_d = elim_var(got_eq_d, formula, var, ex_p)
        got_eq_qn = elim_var(got_eq_qn, formula, var, ex_p)

    # Build And(Eq(d,d2), Eq(qn,qn2))
    ai1 = and_intro(eq_d, eq_qn, [])
    got_dqn = mp(apply_thm(ai1, [], eq_d, Implies(eq_qn, And(eq_d, eq_qn)), got_eq_d),
        got_eq_qn, eq_qn, And(eq_d, eq_qn))
    # Build And(Eq(w,w2), And(Eq(d,d2), Eq(qn,qn2)))
    result = And(eq_w, And(eq_d, eq_qn))
    ai2 = and_intro(eq_w, And(eq_d, eq_qn), [])
    got_result = mp(apply_thm(ai2, [], eq_w, Implies(And(eq_d, eq_qn), result), got_eq_w),
        got_dqn, And(eq_d, eq_qn), result)

    # Close
    for premise in [trans2, trans1, func_d]:
        imp = Implies(premise, got_result.sequent.right[0])
        left = [ff for ff in got_result.sequent.left if not same(ff, premise)]
        got_result = Proof(Sequent(left, [imp]), 'implies_right', [got_result], principal=imp)

    proof = got_result
    for v in [qn2, d2, w2, qn, d, w, sym, q, delta]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'transition_unique'
    return proof




def config_decompose():
    """From two TMConfigs on the same set, derive Eq's on components.
    Pairing |- ∀c,q,h,tape,q2,h2,tape2.
        TMConfig(c,q,h,tape) → TMConfig(c,q2,h2,tape2) →
        And(Eq(q,q2), And(Eq(h,h2), Eq(tape,tape2)))

    Uses ordpair_exists to construct inner pair, tuple_injection on both configs."""
    from core.proof import Proof, Sequent, same
    from tactics import apply_thm, mp, ax, wl, wr, eir, eel, cut
    from theorems.logic import and_intro, and_elim_left, and_elim_right, eq_symmetric
    from theorems.sets import ordpair_exists, ordpair_set_transfer, tuple_injection
    from core.proof import Proof, Sequent
    from core.derived import Exists

    c = Var(postfix='cc')
    q, h, tape = Var(postfix='cq'), Var(postfix='ch'), Var(postfix='ct')
    q2, h2, tape2 = Var(postfix='cq2'), Var(postfix='ch2'), Var(postfix='ct2')

    cfg1 = TMConfig(c, q, h, tape)
    cfg2 = TMConfig(c, q2, h2, tape2)

    # ordpair_exists for both inner pairs
    oe = ordpair_exists()
    v1 = Var(postfix='cv1')
    v2 = Var(postfix='cv2')
    op_v1 = OrdPair(v1, h, tape)
    op_v2 = OrdPair(v2, h2, tape2)
    got_ex_v1 = apply_thm(oe, [h, tape], concl=Exists(v1, op_v1))
    got_ex_v2 = apply_thm(oe, [h2, tape2], concl=Exists(v2, op_v2))

    # Instantiate configs: cfg1 with v1, cfg2 with v2
    op_c_q_v1 = OrdPair(c, q, v1)
    op_c_q2_v2 = OrdPair(c, q2, v2)
    got_inst1 = apply_thm(ax(cfg1), [v1], op_v1, op_c_q_v1, ax(op_v1))
    got_inst2 = apply_thm(ax(cfg2), [v2], op_v2, op_c_q2_v2, ax(op_v2))
    # [cfg1, op_v1] |- OrdPair(c,q,v1)
    # [cfg2, op_v2] |- OrdPair(c,q2,v2)

    # tuple_injection on OrdPair(c,q,v1) and OrdPair(c,q2,v2)
    ti = tuple_injection()
    eq_q = Eq(q, q2)
    eq_v = Eq(v1, v2)
    got_ti1 = apply_thm(ti, [q, v1, q2, v2, c])
    got_ti1 = mp(got_ti1, got_inst1, op_c_q_v1, Implies(op_c_q2_v2, And(eq_q, eq_v)))
    got_ti1 = mp(got_ti1, got_inst2, op_c_q2_v2, And(eq_q, eq_v))

    got_eq_q = apply_thm(and_elim_left(eq_q, eq_v, []), [], And(eq_q, eq_v), eq_q, got_ti1)
    got_eq_v = apply_thm(and_elim_right(eq_q, eq_v, []), [], And(eq_q, eq_v), eq_v, got_ti1)

    # Transfer OrdPair(v1,h,tape) → OrdPair(v2,h,tape) via Eq(v1,v2)
    # ordpair_set_transfer: Eq(s1,s2) → OrdPair(s2,a,b) → OrdPair(s1,a,b)
    # Need Eq(v2,v1) for ordpair_set_transfer(v2, v1, h, tape)
    es = eq_symmetric()
    eq_v_sym = Eq(v2, v1)
    got_eq_v_sym = apply_thm(es, [v1, v2], eq_v, eq_v_sym, got_eq_v)
    ost = ordpair_set_transfer()
    op_v2_ht = OrdPair(v2, h, tape)
    got_op_v2_ht = mp(apply_thm(ost, [v2, v1, h, tape], eq_v_sym,
        Implies(op_v1, op_v2_ht), got_eq_v_sym),
        ax(op_v1), op_v1, op_v2_ht)

    # tuple_injection on OrdPair(v2,h,tape) and OrdPair(v2,h2,tape2)
    eq_h = Eq(h, h2)
    eq_t = Eq(tape, tape2)
    got_ti2 = apply_thm(ti, [h, tape, h2, tape2, v2])
    got_ti2 = mp(got_ti2, got_op_v2_ht, op_v2_ht, Implies(op_v2, And(eq_h, eq_t)))
    got_ti2 = mp(got_ti2, ax(op_v2), op_v2, And(eq_h, eq_t))

    got_eq_h = apply_thm(and_elim_left(eq_h, eq_t, []), [], And(eq_h, eq_t), eq_h, got_ti2)
    got_eq_t = apply_thm(and_elim_right(eq_h, eq_t, []), [], And(eq_h, eq_t), eq_t, got_ti2)

    # Eliminate v1 and v2 existentials from all three Eq proofs
    def elim_var(proof, formula, var, ex_proof):
        p = eel(proof, formula, var)
        return cut(p, Exists(var, formula), ex_proof)

    for ref in [got_eq_q, got_eq_h, got_eq_t]:
        pass  # need to process each

    # Process got_eq_q: has op_v1, op_v2 on left
    got_eq_q = elim_var(got_eq_q, op_v1, v1, got_ex_v1)
    got_eq_q = elim_var(got_eq_q, op_v2, v2, got_ex_v2)
    got_eq_h = elim_var(got_eq_h, op_v1, v1, got_ex_v1)
    got_eq_h = elim_var(got_eq_h, op_v2, v2, got_ex_v2)
    got_eq_t = elim_var(got_eq_t, op_v1, v1, got_ex_v1)
    got_eq_t = elim_var(got_eq_t, op_v2, v2, got_ex_v2)

    # Build And(Eq(h,h2), Eq(tape,tape2))
    ai1 = and_intro(eq_h, eq_t, [])
    got_ht = mp(apply_thm(ai1, [], eq_h, Implies(eq_t, And(eq_h, eq_t)), got_eq_h),
        got_eq_t, eq_t, And(eq_h, eq_t))
    # Build And(Eq(q,q2), And(Eq(h,h2), Eq(tape,tape2)))
    result_and = And(eq_q, And(eq_h, eq_t))
    ai2 = and_intro(eq_q, And(eq_h, eq_t), [])
    got_result = mp(apply_thm(ai2, [], eq_q, Implies(And(eq_h, eq_t), result_and), got_eq_q),
        got_ht, And(eq_h, eq_t), result_and)

    # Close: implies_right + forall_right
    for premise in [cfg2, cfg1]:
        imp = Implies(premise, got_result.sequent.right[0])
        left = [f for f in got_result.sequent.left if not same(f, premise)]
        got_result = Proof(Sequent(left, [imp]), 'implies_right', [got_result], principal=imp)

    proof = got_result
    for v in [tape2, h2, q2, tape, h, q, c]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'config_decompose'
    return proof




def apply_func_transfer():
    """Transfer Apply across function-position Eq.
    Extensionality |- ∀f,g,x,y. Eq(f,g) → Apply(f,x,y) → Apply(g,x,y)

    Apply(f,x,y) = ∃p. OrdPair(p,x,y) ∧ In(p,f). Eq(f,g) via eq_substitution
    gives In(p,f) ↔ In(p,g). Transfer and rebuild."""
    from core.proof import Proof, Sequent, same
    from tactics import apply_thm, mp, ax, wl, eir, eel, cut
    from theorems.logic import and_intro, and_elim_left, and_elim_right
    from theorems.logic import eq_substitution, iff_mp
    from core.proof import Proof, Sequent
    from core.derived import Exists

    f, g, x, y = Var(postfix='af'), Var(postfix='ag'), Var(postfix='ax'), Var(postfix='ay')
    p = Var(postfix='ap')
    eq_fg = Eq(f, g)
    app_f = Apply(f, x, y)
    app_g = Apply(g, x, y)
    op_p = OrdPair(p, x, y)
    in_p_f = In(p, f)
    in_p_g = In(p, g)

    # eq_substitution: Extensionality |- Eq(a,b) → Iff(In(a,z), In(b,z))
    # But we need In(p,f) → In(p,g), which is Iff(In(f,p), In(g,p))... no.
    # eq_substitution gives Leibniz: In(f,z) ↔ In(g,z). We need In(p,f) ↔ In(p,g).
    # Eq(f,g) = ∀z. In(z,f) ↔ In(z,g) by definition. Instantiate z=p directly.
    iff_in = Iff(in_p_f, in_p_g)
    got_iff = apply_thm(ax(eq_fg), [p], concl=iff_in)
    # [Eq(f,g)] |- Iff(In(p,f), In(p,g))

    got_fwd = apply_thm(iff_mp(in_p_f, in_p_g, []), [],
        iff_in, Implies(in_p_f, in_p_g), got_iff)
    got_in_g = mp(got_fwd, ax(in_p_f), in_p_f, in_p_g)
    # [Eq(f,g), In(p,f)] |- In(p,g)

    # Build And(OrdPair(p,x,y), In(p,g)) → eir → Apply(g,x,y)
    ai = and_intro(op_p, in_p_g, [])
    got_and = mp(apply_thm(ai, [], op_p, Implies(in_p_g, And(op_p, in_p_g)), ax(op_p)),
        got_in_g, in_p_g, And(op_p, in_p_g))
    got_app_g = eir(got_and, And(op_p, in_p_g), p, p)
    # [Eq(f,g), In(p,f), OrdPair(p,x,y)] |- Apply(g,x,y)

    # Merge OrdPair(p,x,y) + In(p,f) into And, eel p
    and_pf = And(op_p, in_p_f)
    got_op = apply_thm(and_elim_left(op_p, in_p_f, []), [], and_pf, op_p, ax(and_pf))
    got_in = apply_thm(and_elim_right(op_p, in_p_f, []), [], and_pf, in_p_f, ax(and_pf))
    got_app_g = cut(got_app_g, op_p, got_op)
    got_app_g = cut(got_app_g, in_p_f, got_in)
    got_app_g = eel(got_app_g, and_pf, p)
    # [Eq(f,g), Apply(f,x,y)] |- Apply(g,x,y)

    # Close
    for premise in [app_f, eq_fg]:
        imp = Implies(premise, got_app_g.sequent.right[0])
        left = [ff for ff in got_app_g.sequent.left if not same(ff, premise)]
        got_app_g = Proof(Sequent(left, [imp]), 'implies_right', [got_app_g], principal=imp)

    proof = got_app_g
    for v in [y, x, g, f]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'apply_func_transfer'
    return proof




def tape_update_unique():
    """Two TapeUpdates with same args give equal tapes.
    |- forall t1, t2, tape, h, w.
        TapeUpdate(t1, tape, h, w) -> TapeUpdate(t2, tape, h, w) -> Eq(t1, t2)

    Both TapeUpdates give same Iff characterization. Chain Iffs to get
    In(p,t1) ↔ In(p,t2), which IS Eq(t1,t2)."""
    from core.proof import Proof, Sequent, same
    from tactics import apply_thm, mp, ax
    from theorems.logic import iff_mp, iff_mp_rev, iff_intro
    from core.proof import Proof, Sequent

    t1, t2, tape, h, w = Var(postfix='tu1'), Var(postfix='tu2'), Var(postfix='tp'), Var(postfix='hd'), Var(postfix='wr')
    p = Var(postfix='ep')
    yv = Var(postfix='ey')
    tu1 = TapeUpdate(t1, tape, h, w)
    tu2 = TapeUpdate(t2, tape, h, w)

    in_p_t1 = In(p, t1)
    in_p_t2 = In(p, t2)
    op_phw = OrdPair(p, h, w)
    op_phy = OrdPair(p, h, yv)
    not_ex_y = Not(Exists(yv, op_phy))
    right_and = And(In(p, tape), not_ex_y)
    or_form = Or(op_phw, right_and)
    iff1 = Iff(in_p_t1, or_form)
    iff2 = Iff(in_p_t2, or_form)

    # From tu1: In(p,t1) ↔ Or(...)
    got_iff1 = apply_thm(ax(tu1), [p], concl=iff1)
    # From tu2: In(p,t2) ↔ Or(...)
    got_iff2 = apply_thm(ax(tu2), [p], concl=iff2)

    # Forward: In(p,t1) → Or → In(p,t2)
    got_fwd1 = apply_thm(iff_mp(in_p_t1, or_form, []), [],
        iff1, Implies(in_p_t1, or_form), got_iff1)
    got_or = mp(got_fwd1, ax(in_p_t1), in_p_t1, or_form)
    got_rev2 = apply_thm(iff_mp_rev(in_p_t2, or_form, []), [],
        iff2, Implies(or_form, in_p_t2), got_iff2)
    got_fwd = mp(got_rev2, got_or, or_form, in_p_t2)
    # [tu1, tu2, In(p,t1)] |- In(p,t2)

    # Backward: In(p,t2) → Or → In(p,t1)
    got_fwd2 = apply_thm(iff_mp(in_p_t2, or_form, []), [],
        iff2, Implies(in_p_t2, or_form), got_iff2)
    got_or2 = mp(got_fwd2, ax(in_p_t2), in_p_t2, or_form)
    got_rev1 = apply_thm(iff_mp_rev(in_p_t1, or_form, []), [],
        iff1, Implies(or_form, in_p_t1), got_iff1)
    got_back = mp(got_rev1, got_or2, or_form, in_p_t1)
    # [tu1, tu2, In(p,t2)] |- In(p,t1)

    # Iff(In(p,t1), In(p,t2))
    ii = iff_intro(in_p_t1, in_p_t2, [])
    imp_fwd = Implies(in_p_t1, in_p_t2)
    fwd_left = [f for f in got_fwd.sequent.left if not same(f, in_p_t1)]
    got_imp_fwd = Proof(Sequent(fwd_left, [imp_fwd]),
        'implies_right', [got_fwd], principal=imp_fwd)
    imp_back = Implies(in_p_t2, in_p_t1)
    back_left = [f for f in got_back.sequent.left if not same(f, in_p_t2)]
    got_imp_back = Proof(Sequent(back_left, [imp_back]),
        'implies_right', [got_back], principal=imp_back)

    iff_t1t2 = Iff(in_p_t1, in_p_t2)
    got_iff_final = mp(apply_thm(ii, [], imp_fwd,
        Implies(imp_back, iff_t1t2), got_imp_fwd),
        got_imp_back, imp_back, iff_t1t2)

    # forall_right p → Eq(t1, t2)
    fa_iff = Forall(p, iff_t1t2)
    got_eq = Proof(Sequent(got_iff_final.sequent.left, [fa_iff]),
        'forall_right', [got_iff_final], principal=fa_iff, term=p)
    # [tu1, tu2] |- Eq(t1, t2)

    # Close
    for premise in [tu2, tu1]:
        imp = Implies(premise, got_eq.sequent.right[0])
        left = [f for f in got_eq.sequent.left if not same(f, premise)]
        got_eq = Proof(Sequent(left, [imp]), 'implies_right', [got_eq], principal=imp)

    proof = got_eq
    for v in [w, h, tape, t2, t1]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'tape_update_unique'
    return proof




def tape_update_eq_args():
    """TapeUpdate transfers across Eq on args.
    |- forall t1, t2, tape1, h1, w1, tape2, h2, w2.
        TapeUpdate(t1, tape1, h1, w1) -> TapeUpdate(t2, tape2, h2, w2) ->
        Eq(tape1, tape2) -> Eq(h1, h2) -> Eq(w1, w2) ->
        Eq(t1, t2)

    Both TapeUpdates give Iff characterizations. With Eq on args,
    the RHS's are equivalent. Chain to get In(p,t1) ↔ In(p,t2)."""
    from core.proof import Proof, Sequent, same
    from tactics import apply_thm, mp, ax, wl, wr, fl, eir, eel, cut
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_intro, iff_mp, iff_mp_rev, eq_substitution)
    from theorems.sets import ordpair_eq_transfer
    from core.proof import Proof, Sequent

    t1, t2 = Var(postfix='tu1'), Var(postfix='tu2')
    tape1, h1, w1 = Var(postfix='tp1'), Var(postfix='hd1'), Var(postfix='wr1')
    tape2, h2, w2 = Var(postfix='tp2'), Var(postfix='hd2'), Var(postfix='wr2')
    pv = Var(postfix='ep')
    yv = Var(postfix='ey')

    tu1 = TapeUpdate(t1, tape1, h1, w1)
    tu2 = TapeUpdate(t2, tape2, h2, w2)
    eq_tp = Eq(tape1, tape2)
    eq_hd = Eq(h1, h2)
    eq_wr = Eq(w1, w2)

    in_pv_t1 = In(pv, t1)
    in_pv_t2 = In(pv, t2)

    # tu1 Iff components
    op1 = OrdPair(pv, h1, w1)
    op1y = OrdPair(pv, h1, yv)
    not_ex1 = Not(Exists(yv, op1y))
    right1 = And(In(pv, tape1), not_ex1)
    or1 = Or(op1, right1)
    iff1 = Iff(in_pv_t1, or1)
    got_iff1 = apply_thm(ax(tu1), [pv], concl=iff1)

    # tu2 Iff components
    op2 = OrdPair(pv, h2, w2)
    yv2 = Var(postfix='ey2')
    op2y = OrdPair(pv, h2, yv2)
    not_ex2 = Not(Exists(yv2, op2y))
    right2 = And(In(pv, tape2), not_ex2)
    or2 = Or(op2, right2)
    iff2 = Iff(in_pv_t2, or2)
    got_iff2 = apply_thm(ax(tu2), [pv], concl=iff2)

    # === Forward: In(pv,t1) → In(pv,t2) ===
    # In(pv,t1) → or1 → or2 → In(pv,t2)
    # or1 → or2: transfer OrdPair(pv,h1,w1) to OrdPair(pv,h2,w2) via Eq(h1,h2), Eq(w1,w2)
    #            transfer In(pv,tape1) to In(pv,tape2) via Eq(tape1,tape2)
    #            transfer OrdPair(pv,h1,yv) to OrdPair(pv,h2,yv) via Eq(h1,h2)

    # or1 = Implies(Not(op1), right1). Assume Not(op1) and right1.
    # Need or2 = Implies(Not(op2), right2). Need to show right2 under assumption Not(op2).

    # Direction: or1 → or2 is hard to do directly via Or = Implies(Not,.).
    # Easier: use the Iff characterizations.
    # In(pv,t1) → or1 (via iff1 fwd). From or1, derive or2 (via Eq transfers). or2 → In(pv,t2) (via iff2 rev).
    # or1 → or2: Or(A1,B1) → Or(A2,B2) where A1↔A2 and B1↔B2.
    # Or(A,B) = Implies(Not(A),B). Assume Not(A2). Need B2.
    # From Not(A2): Not(OrdPair(pv,h2,w2)).
    # Transfer to Not(OrdPair(pv,h1,w1))? No — we need the REVERSE: Not(A2) + A1↔A2 → Not(A1).
    # From Eq(h1,h2)+Eq(w1,w2): OrdPair(pv,h1,w1) ↔ OrdPair(pv,h2,w2).
    # ordpair_eq_transfer: Eq(a,c)+Eq(b,d) → OrdPair(t,a,b) → OrdPair(t,c,d)
    # So OrdPair(pv,h1,w1) → OrdPair(pv,h2,w2). Contrapositive: Not(OrdPair(pv,h2,w2)) → Not(OrdPair(pv,h1,w1)).

    # Forward: Not(OrdPair(pv,h2,w2)) → Not(OrdPair(pv,h1,w1))
    # Proof: assume OrdPair(pv,h1,w1). Transfer → OrdPair(pv,h2,w2). Contradiction.
    oet = ordpair_eq_transfer()
    got_op_transfer = apply_thm(oet, [h1, w1, h2, w2, pv])
    got_op_transfer = mp(got_op_transfer, ax(eq_hd), eq_hd, got_op_transfer.sequent.right[0].right)
    got_op_transfer = mp(got_op_transfer, ax(eq_wr), eq_wr, Implies(op1, op2))
    # [Eq(h1,h2), Eq(w1,w2)] |- OrdPair(pv,h1,w1) → OrdPair(pv,h2,w2)

    got_op12 = mp(got_op_transfer, ax(op1), op1, op2)
    # Contrapositive: Not(op2) + op1 → ⊥
    not_op2 = Not(op2)
    got_bot = Proof(Sequent(list(got_op12.sequent.left) + [not_op2], []),
        'not_left', [got_op12], principal=not_op2)
    not_op1 = Not(op1)
    got_not_op1 = Proof(Sequent([f for f in got_bot.sequent.left if not same(f, op1)],
        [not_op1]), 'not_right', [got_bot], principal=not_op1)
    # [Eq(h1,h2), Eq(w1,w2), Not(op2)] |- Not(op1)

    # or1 = Implies(Not(op1), right1). With Not(op1), get right1.
    # But or1 comes from In(pv,t1). Let me chain properly:
    # In(pv,t1) → iff1 fwd → or1. Or1 = Implies(Not(op1), right1).
    # With Not(op1): mp(or1, Not(op1)) → right1.
    got_fwd1 = apply_thm(iff_mp(in_pv_t1, or1, []), [],
        iff1, Implies(in_pv_t1, or1), got_iff1)
    got_or1 = mp(got_fwd1, ax(in_pv_t1), in_pv_t1, or1)
    # [tu1, In(pv,t1)] |- or1

    # or1 + Not(op1) → right1 = And(In(pv,tape1), not_ex1)
    got_right1 = mp(got_or1, got_not_op1, not_op1, right1)
    # [tu1, In(pv,t1), Eq(h1,h2), Eq(w1,w2), Not(op2)] |- right1

    # From right1, build right2:
    # right1 = And(In(pv,tape1), Not(Exists(yv, OrdPair(pv,h1,yv))))
    # right2 = And(In(pv,tape2), Not(Exists(yv2, OrdPair(pv,h2,yv2))))
    got_in_tape1 = apply_thm(and_elim_left(In(pv, tape1), not_ex1, []), [],
        right1, In(pv, tape1), got_right1)
    got_not_ex1 = apply_thm(and_elim_right(In(pv, tape1), not_ex1, []), [],
        right1, not_ex1, got_right1)

    # In(pv,tape1) → In(pv,tape2) via eq_substitution
    es = eq_substitution()
    iff_in_tp = Iff(In(pv, tape1), In(pv, tape2))
    got_iff_tp = apply_thm(es, [tape1, tape2, pv])  # Eq(tape1,tape2) → Iff
    # Wait, eq_substitution is Eq(a,b) → Iff(In(a,c), In(b,c)).
    # That's membership IN a set. I need In(pv, tape1) → In(pv, tape2).
    # That's Eq(tape1,tape2) → Iff(In(pv,tape1), In(pv,tape2)).
    # eq_substitution: ∀a,b,c. Eq(a,b) → Iff(In(a,c), In(b,c)).
    # This gives In(tape1,c) ↔ In(tape2,c). Not what I need.
    # I need In(pv,tape1) ↔ In(pv,tape2). That's just Eq(tape1,tape2) expanded!
    # Eq(tape1,tape2) = ∀x. In(x,tape1) ↔ In(x,tape2). Instantiate with pv.

    got_iff_tp = fl(eq_tp, Iff(In(pv, tape1), In(pv, tape2)), pv)
    # [Eq(tape1,tape2)] |- Iff(In(pv,tape1), In(pv,tape2))
    got_in_tape2 = mp(apply_thm(iff_mp(In(pv, tape1), In(pv, tape2), []), [],
        Iff(In(pv, tape1), In(pv, tape2)),
        Implies(In(pv, tape1), In(pv, tape2)), got_iff_tp),
        got_in_tape1, In(pv, tape1), In(pv, tape2))

    # Not(Exists(yv,OrdPair(pv,h1,yv))) → Not(Exists(yv2,OrdPair(pv,h2,yv2)))
    # Contrapositive: Exists(yv2,OrdPair(pv,h2,yv2)) → Exists(yv,OrdPair(pv,h1,yv))
    # From OrdPair(pv,h2,yv2) + Eq(h2,h1) = reverse(Eq(h1,h2)):
    from theorems.logic import eq_symmetric as eq_sym_thm
    esym = eq_sym_thm()
    eq_hd_rev = Eq(h2, h1)
    got_eq_hd_rev = apply_thm(esym, [h1, h2], eq_hd, eq_hd_rev, ax(eq_hd))

    # ordpair_eq_transfer: Eq(h2,h1) + Eq(yv2,yv2) → OrdPair(pv,h2,yv2) → OrdPair(pv,h1,yv2)
    # Wait, I need OrdPair with h1 not h2. And yv2 stays.
    # ordpair_eq_transfer transfers first+second components: Eq(a,c)+Eq(b,d) → OrdPair(t,a,b) → OrdPair(t,c,d)
    # Here: Eq(h2,h1) + Eq(yv2,yv2) → OrdPair(pv,h2,yv2) → OrdPair(pv,h1,yv2)
    from theorems.logic import eq_reflexive
    er = eq_reflexive()
    eq_yy = Eq(yv2, yv2)
    got_eq_yy = apply_thm(er, [yv2], concl=eq_yy)
    op_pv_h1_yv2 = OrdPair(pv, h1, yv2)
    got_op_rev = apply_thm(oet, [h2, yv2, h1, yv2, pv])
    got_op_rev = mp(got_op_rev, got_eq_hd_rev, eq_hd_rev, got_op_rev.sequent.right[0].right)
    r = got_op_rev.sequent.right[0]
    got_op_rev = mp(got_op_rev, got_eq_yy, r.left, r.right)
    r = got_op_rev.sequent.right[0]
    got_op_h1 = mp(got_op_rev, ax(r.left), r.left, r.right)
    # [Eq(h1,h2), OrdPair(pv,h2,yv2)] |- OrdPair(pv,h1,yv2)

    # eir(proof, body, var, witness): body has var, proof proves body[var:=witness], result is ∃var.body
    got_ex_h1 = eir(got_op_h1, op1y, yv, yv2)
    # But we need ex_h1 = Exists(yv, OrdPair(pv,h1,yv)). eir gives Exists(yv, op1y) ✓.

    # eel yv2 from OrdPair(pv,h2,yv2) on left
    got_ex_h1 = eel(got_ex_h1, op2y, yv2)
    # [..., Exists(yv2, OrdPair(pv,h2,yv2))] |- Exists(yv, OrdPair(pv,h1,yv))

    # Contrapositive: Not(Exists(yv,...)) → Not(Exists(yv2,...))
    ex_h2 = Exists(yv2, op2y)
    # got_ex_h1: [Eq(h1,h2), Exists(yv2,...)] |- Exists(yv,...)
    # Want: Not(Exists(yv,...)) + Exists(yv2,...) → ⊥
    got_bot2 = Proof(Sequent(list(got_ex_h1.sequent.left) + [not_ex1], []),
        'not_left', [got_ex_h1], principal=not_ex1)
    got_not_ex2 = Proof(Sequent([f for f in got_bot2.sequent.left if not same(f, ex_h2)],
        [not_ex2]), 'not_right', [got_bot2], principal=not_ex2)
    # [Eq(h1,h2), Not(Exists(yv,OrdPair(pv,h1,yv)))] |- Not(Exists(yv2,OrdPair(pv,h2,yv2)))

    # Combine: got_not_ex2 uses got_not_ex1 from right1
    got_not_ex2_from = cut(got_not_ex2, not_ex1, got_not_ex1)
    # [tu1, In(pv,t1), Eq(h1,h2), Eq(w1,w2), Not(op2)] |- not_ex2

    # Build right2 = And(In(pv,tape2), not_ex2)
    ai = and_intro(In(pv, tape2), not_ex2, [])
    got_right2 = mp(apply_thm(ai, [], In(pv, tape2), Implies(not_ex2, right2), got_in_tape2),
        got_not_ex2_from, not_ex2, right2)

    # or2 = Implies(Not(op2), right2). Discharge Not(op2):
    got_or2 = Proof(Sequent(
        [f for f in got_right2.sequent.left if not same(f, not_op2)],
        [or2]), 'implies_right', [got_right2], principal=or2)

    # or2 → In(pv,t2) via iff2 rev
    got_rev2 = apply_thm(iff_mp_rev(in_pv_t2, or2, []), [],
        iff2, Implies(or2, in_pv_t2), got_iff2)
    got_fwd_final = mp(got_rev2, got_or2, or2, in_pv_t2)
    # [tu1, tu2, In(pv,t1), Eq(h1,h2), Eq(w1,w2), Eq(tape1,tape2)] |- In(pv,t2)

    # === Backward: In(pv,t2) → In(pv,t1) ===
    # Symmetric: swap 1↔2 roles. Transfer or2 → or1 using reverse Eq's.
    # For brevity, I'll use the same structure but reversed.

    # Reverse Eq's
    eq_hd_12 = eq_hd  # Eq(h1,h2) — for the reverse direction, need Eq(h2,h1)
    # But we already have got_eq_hd_rev = Eq(h2,h1). And eq_wr reverse:
    eq_wr_rev = Eq(w2, w1)
    got_eq_wr_rev = apply_thm(esym, [w1, w2], eq_wr, eq_wr_rev, ax(eq_wr))
    eq_tp_rev = Eq(tape2, tape1)
    got_eq_tp_rev = apply_thm(esym, [tape1, tape2], eq_tp, eq_tp_rev, ax(eq_tp))

    # Not(op1) from Not(op2) + OrdPair(pv,h2,w2)→OrdPair(pv,h1,w1)
    got_op_rev2 = apply_thm(oet, [h2, w2, h1, w1, pv])
    got_op_rev2 = mp(got_op_rev2, got_eq_hd_rev, eq_hd_rev, got_op_rev2.sequent.right[0].right)
    r = got_op_rev2.sequent.right[0]
    got_op_rev2 = mp(got_op_rev2, got_eq_wr_rev, r.left, r.right)
    r = got_op_rev2.sequent.right[0]
    got_op21 = mp(got_op_rev2, ax(r.left), r.left, r.right)
    not_op1_f = Not(op1)
    got_bot3 = Proof(Sequent(list(got_op21.sequent.left) + [not_op1_f], []),
        'not_left', [got_op21], principal=not_op1_f)
    not_op2_f = Not(op2)
    got_not_op2 = Proof(Sequent([f for f in got_bot3.sequent.left if not same(f, op2)],
        [not_op2_f]), 'not_right', [got_bot3], principal=not_op2_f)

    # In(pv,t2) → or2 → right2 (with Not(op2))
    got_fwd2 = apply_thm(iff_mp(in_pv_t2, or2, []), [],
        iff2, Implies(in_pv_t2, or2), got_iff2)
    got_or2_back = mp(got_fwd2, ax(in_pv_t2), in_pv_t2, or2)
    got_right2_back = mp(got_or2_back, got_not_op2, not_op2_f, right2)

    got_in_tape2_back = apply_thm(and_elim_left(In(pv, tape2), not_ex2, []), [],
        right2, In(pv, tape2), got_right2_back)
    got_not_ex2_back = apply_thm(and_elim_right(In(pv, tape2), not_ex2, []), [],
        right2, not_ex2, got_right2_back)

    # In(pv,tape2) → In(pv,tape1) via Eq(tape2,tape1)
    got_iff_tp_rev = fl(eq_tp_rev, Iff(In(pv, tape2), In(pv, tape1)), pv)
    got_in_tape1_back = mp(apply_thm(iff_mp(In(pv, tape2), In(pv, tape1), []), [],
        Iff(In(pv, tape2), In(pv, tape1)),
        Implies(In(pv, tape2), In(pv, tape1)), got_iff_tp_rev),
        got_in_tape2_back, In(pv, tape2), In(pv, tape1))

    # Not(Exists(yv2,OrdPair(pv,h2,yv2))) → Not(Exists(yv,OrdPair(pv,h1,yv)))
    eq_hd_fwd = eq_hd  # Eq(h1,h2)
    eq_yy_back = apply_thm(er, [yv], concl=Eq(yv, yv))
    op_pv_h2_yv = OrdPair(pv, h2, yv)
    got_op_h2 = apply_thm(oet, [h1, yv, h2, yv, pv])
    got_op_h2 = mp(got_op_h2, ax(eq_hd), eq_hd, got_op_h2.sequent.right[0].right)
    r = got_op_h2.sequent.right[0]
    got_op_h2 = mp(got_op_h2, eq_yy_back, r.left, r.right)
    r = got_op_h2.sequent.right[0]
    got_op_h2_from1 = mp(got_op_h2, ax(r.left), r.left, r.right)
    # eir yv as yv2
    got_ex_h2_back = eir(got_op_h2_from1, op2y, yv2, yv)
    got_ex_h2_back = eel(got_ex_h2_back, op1y, yv)
    # [Eq(h1,h2), Exists(yv,...)] |- Exists(yv2,...)

    ex_h1_f = Exists(yv, op1y)
    got_bot4 = Proof(Sequent(list(got_ex_h2_back.sequent.left) + [not_ex2], []),
        'not_left', [got_ex_h2_back], principal=not_ex2)
    got_not_ex1_back = Proof(Sequent([f for f in got_bot4.sequent.left if not same(f, ex_h1_f)],
        [not_ex1]), 'not_right', [got_bot4], principal=not_ex1)
    got_not_ex1_from = cut(got_not_ex1_back, not_ex2, got_not_ex2_back)

    # Build right1 = And(In(pv,tape1), not_ex1)
    ai_back = and_intro(In(pv, tape1), not_ex1, [])
    got_right1_back = mp(apply_thm(ai_back, [], In(pv, tape1), Implies(not_ex1, right1), got_in_tape1_back),
        got_not_ex1_from, not_ex1, right1)

    # or1 = Implies(Not(op1), right1). Discharge Not(op1):
    got_or1_back = Proof(Sequent(
        [f for f in got_right1_back.sequent.left if not same(f, not_op1_f)],
        [or1]), 'implies_right', [got_right1_back], principal=or1)

    got_rev1 = apply_thm(iff_mp_rev(in_pv_t1, or1, []), [],
        iff1, Implies(or1, in_pv_t1), got_iff1)
    got_back_final = mp(got_rev1, got_or1_back, or1, in_pv_t1)
    # [tu1, tu2, In(pv,t2), Eq(...)] |- In(pv,t1)

    # === Iff(In(pv,t1), In(pv,t2)) ===
    ii = iff_intro(in_pv_t1, in_pv_t2, [])
    imp_fwd = Implies(in_pv_t1, in_pv_t2)
    fwd_left = [f for f in got_fwd_final.sequent.left if not same(f, in_pv_t1)]
    got_imp_fwd = Proof(Sequent(fwd_left, [imp_fwd]),
        'implies_right', [got_fwd_final], principal=imp_fwd)
    imp_back = Implies(in_pv_t2, in_pv_t1)
    back_left = [f for f in got_back_final.sequent.left if not same(f, in_pv_t2)]
    got_imp_back = Proof(Sequent(back_left, [imp_back]),
        'implies_right', [got_back_final], principal=imp_back)

    iff_t1t2 = Iff(in_pv_t1, in_pv_t2)
    got_iff_final = mp(apply_thm(ii, [], imp_fwd,
        Implies(imp_back, iff_t1t2), got_imp_fwd),
        got_imp_back, imp_back, iff_t1t2)

    # forall_right pv → Eq(t1, t2)
    fa_iff = Forall(pv, iff_t1t2)
    got_eq = Proof(Sequent(got_iff_final.sequent.left, [fa_iff]),
        'forall_right', [got_iff_final], principal=fa_iff, term=pv)

    # Cut reverse Eq's with forward Eq proofs
    if any(same(eq_tp_rev, f) for f in got_eq.sequent.left):
        got_eq = cut(got_eq, eq_tp_rev, got_eq_tp_rev)
    if any(same(eq_hd_rev, f) for f in got_eq.sequent.left):
        got_eq = cut(got_eq, eq_hd_rev, got_eq_hd_rev)
    if any(same(eq_wr_rev, f) for f in got_eq.sequent.left):
        got_eq = cut(got_eq, eq_wr_rev, got_eq_wr_rev)

    # Close: implies_right for all premises, forall_right for all vars
    for premise in [eq_wr, eq_hd, eq_tp, tu2, tu1]:
        imp = Implies(premise, got_eq.sequent.right[0])
        left = [f for f in got_eq.sequent.left if not same(f, premise)]
        got_eq = Proof(Sequent(left, [imp]), 'implies_right', [got_eq], principal=imp)

    proof = got_eq
    for v in [w2, h2, tape2, w1, h1, tape1, t2, t1]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'tape_update_eq_args'
    return proof





def headmove_right_elim():
    """Extract Eq(hn,ska) from HeadMove in the right-move case.
    Pairing |- ∀h,hn,d,ka,ska,d1.
        HeadMove(h,hn,d) → Eq(h,ka) → Eq(d,d1) → Num(d1,1) →
        Successor(ska,ka) → Eq(hn,ska)

    HeadMove = Or(And(Num(d,1),Succ(hn,h)), And(Num(d,0),Succ(h,hn))).
    Left case: transfer Succ(hn,h) to Succ(hn,ka), unique_successor → Eq(hn,ska).
    Right case: Num(d,0) + Eq(d,d1) + Num(d1,1) → zero_neq_one → contradiction."""
    from tactics import apply_thm, mp, ax, wl, wr, fl, cut
    from theorems.logic import and_elim_left, and_elim_right, or_elim
    from theorems.sets import unique_successor, ordpair_val_transfer
    from theorems.tm import zero_neq_one
    from core.proof import Proof, Sequent, same
    from core.derived import Exists

    h, hn, d = Var(postfix='hh'), Var(postfix='hhn'), Var(postfix='hd')
    ka, ska, d1 = Var(postfix='hka'), Var(postfix='hska'), Var(postfix='hd1')

    hm = HeadMove(h, hn, d)
    eq_h_ka = Eq(h, ka)
    eq_d_d1 = Eq(d, d1)
    num_d1 = Num(d1, 1)
    succ_ska = Successor(ska, ka)
    eq_hn_ska = Eq(hn, ska)

    left_and = And(Num(d, 1), Successor(hn, h))
    right_and = And(Num(d, 0), Successor(h, hn))

    # --- Left case: And(Num(d,1), Succ(hn,h)) → Eq(hn,ska) ---
    # Succ(hn,h): ∀z. z∈hn ↔ Or(z∈h, z=h)
    # Succ(ska,ka): ∀z. z∈ska ↔ Or(z∈ka, z=ka)
    # Eq(h,ka): ∀z. z∈h ↔ z∈ka (and eq_in_eq: z=h ↔ z=ka)
    # So z∈hn ↔ z∈ska for all z → Eq(hn,ska).

    got_succ_hnh = apply_thm(and_elim_right(Num(d,1), Successor(hn,h), []), [],
        left_and, Successor(hn, h), ax(left_and))
    # [left_and] |- Successor(hn, h)

    from theorems.logic import iff_chain, iff_mp, iff_mp_rev
    from theorems.sets import eq_in_eq
    from theorems.logic import or_iff_compat

    z = Var(postfix='hz')
    # From Succ(hn,h): Iff(In(z,hn), Or(In(z,h), Eq(z,h)))
    iff_hn = Iff(In(z, hn), Or(In(z, h), Eq(z, h)))
    got_iff_hn = apply_thm(ax(Successor(hn, h)), [z], concl=iff_hn)
    # [Succ(hn,h)] |- Iff(In(z,hn), Or(In(z,h), Eq(z,h)))

    # From Succ(ska,ka): Iff(In(z,ska), Or(In(z,ka), Eq(z,ka)))
    iff_ska = Iff(In(z, ska), Or(In(z, ka), Eq(z, ka)))
    got_iff_ska = apply_thm(ax(succ_ska), [z], concl=iff_ska)
    # [Succ(ska,ka)] |- Iff(In(z,ska), Or(In(z,ka), Eq(z,ka)))

    # From Eq(h,ka): Iff(In(z,h), In(z,ka))
    iff_in_hka = Iff(In(z, h), In(z, ka))
    got_iff_in = apply_thm(ax(eq_h_ka), [z], concl=iff_in_hka)
    # [Eq(h,ka)] |- Iff(In(z,h), In(z,ka))

    # eq_in_eq: ∀x1,x2. Eq(x1,x2) → ∀z. Iff(Eq(z,x1), Eq(z,x2))
    eie = eq_in_eq()
    iff_eq_hka = Iff(Eq(z, h), Eq(z, ka))
    got_eie = apply_thm(eie, [h, ka], eq_h_ka,
        Forall(z, iff_eq_hka), ax(eq_h_ka))
    got_iff_eq = apply_thm(got_eie, [z], concl=iff_eq_hka)
    # [Eq(h,ka)] |- Iff(Eq(z,h), Eq(z,ka))

    # or_iff_compat(P,Q,R,S): Iff(P,R) → Iff(Q,S) → Iff(Or(P,Q), Or(R,S))
    oic = or_iff_compat(In(z,h), Eq(z,h), In(z,ka), Eq(z,ka), [])
    iff_or = Iff(Or(In(z,h), Eq(z,h)), Or(In(z,ka), Eq(z,ka)))
    got_iff_or = mp(apply_thm(oic, [], iff_in_hka,
        Implies(iff_eq_hka, iff_or), got_iff_in),
        got_iff_eq, iff_eq_hka, iff_or)
    # [Eq(h,ka)] |- Iff(Or(In(z,h),Eq(z,h)), Or(In(z,ka),Eq(z,ka)))

    # Chain: In(z,hn) ↔ Or(In(z,h),Eq(z,h)) ↔ Or(In(z,ka),Eq(z,ka)) ↔ In(z,ska)
    # iff_chain: Iff(A,B) → Iff(B,C) → Iff(A,C)
    ic = iff_chain(In(z,hn), Or(In(z,h),Eq(z,h)), Or(In(z,ka),Eq(z,ka)), [])
    iff_hn_or2 = Iff(In(z,hn), Or(In(z,ka), Eq(z,ka)))
    got_iff_hn_or2 = mp(apply_thm(ic, [], iff_hn,
        Implies(iff_or, iff_hn_or2), got_iff_hn),
        got_iff_or, iff_or, iff_hn_or2)

    # Reverse iff_ska: Iff(In(z,ska), Or(...)) → Iff(Or(...), In(z,ska))
    from theorems.logic import iff_sym
    isym = iff_sym(In(z,ska), Or(In(z,ka), Eq(z,ka)), [])
    iff_or_ska = Iff(Or(In(z,ka), Eq(z,ka)), In(z, ska))
    got_iff_or_ska = apply_thm(isym, [], iff_ska, iff_or_ska, got_iff_ska)

    # Chain: In(z,hn) ↔ Or(In(z,ka),Eq(z,ka)) ↔ In(z,ska)
    ic2 = iff_chain(In(z,hn), Or(In(z,ka),Eq(z,ka)), In(z,ska), [])
    iff_hn_ska = Iff(In(z, hn), In(z, ska))
    got_iff_hn_ska = mp(apply_thm(ic2, [], iff_hn_or2,
        Implies(iff_or_ska, iff_hn_ska), got_iff_hn_or2),
        got_iff_or_ska, iff_or_ska, iff_hn_ska)
    # [Succ(hn,h), Eq(h,ka), Succ(ska,ka)] |- Iff(In(z,hn), In(z,ska))

    # forall z → Eq(hn,ska)
    fa_iff = Forall(z, iff_hn_ska)
    got_fa = Proof(Sequent(got_iff_hn_ska.sequent.left, [fa_iff]),
        'forall_right', [got_iff_hn_ska], principal=fa_iff, term=z)
    # [...] |- ∀z. Iff(In(z,hn), In(z,ska)) = Eq(hn,ska)

    # Cut Successor(hn,h) from got_fa left with got_succ_hnh
    got_left = cut(got_fa, Successor(hn, h), got_succ_hnh)
    # [left_and, Eq(h,ka), Succ(ska,ka)] |- Eq(hn,ska)

    # --- Right case: And(Num(d,0), Succ(h,hn)) → contradiction → Eq(hn,ska) ---
    # Num(d,0) = Empty(d). Num(d1,1) = ∀m. Empty(m) → Succ(d1,m).
    # Instantiate Num(d1,1) with d: Empty(d) → Succ(d1,d).
    # zero_neq_one(d, d1, d): Empty(d) → Succ(d1,d) → ¬Eq(d,d1). Contradiction.

    got_numd0 = apply_thm(and_elim_left(Num(d,0), Successor(h,hn), []), [],
        right_and, Num(d,0), ax(right_and))
    # [right_and] |- Empty(d)

    succ_d1_d = Successor(d1, d)
    got_succ_d1 = fl(num_d1, Implies(Num(d,0), succ_d1_d), d)
    got_succ_d1 = cut(got_succ_d1, num_d1, ax(num_d1))
    got_succ_d1 = mp(got_succ_d1, got_numd0, Num(d,0), succ_d1_d)
    # [right_and, Num(d1,1)] |- Succ(d1, d)

    zno = zero_neq_one()
    not_eq_d_d1 = Not(eq_d_d1)
    got_zno = apply_thm(zno, [d, d1, d])
    got_zno = mp(got_zno, got_numd0, Num(d,0), got_zno.sequent.right[0].right)
    got_zno = mp(got_zno, got_succ_d1, succ_d1_d, not_eq_d_d1)
    # [right_and, Num(d1,1)] |- ¬Eq(d, d1)

    got_eq_dd1 = ax(eq_d_d1)
    got_eq_dd1_w = wl(got_eq_dd1, *got_zno.sequent.left)
    ctx_right = list(got_eq_dd1_w.sequent.left)
    got_bot_r = Proof(Sequent(ctx_right + [not_eq_d_d1], []),
        'not_left', [got_eq_dd1_w], principal=not_eq_d_d1)
    from tactics import weaken_to
    ps0 = weaken_to(got_zno, ctx_right)
    got_bot_r = Proof(Sequent(ctx_right, []), 'cut',
        [ps0, got_bot_r], principal=not_eq_d_d1)
    got_right_case = Proof(Sequent(got_bot_r.sequent.left, [eq_hn_ska]),
        'weakening_right', [got_bot_r], principal=eq_hn_ska)
    # [right_and, Num(d1,1), Eq(d,d1)] |- eq_hn_ska

    # --- Or-elim to combine both cases ---
    oe = or_elim(left_and, right_and, eq_hn_ska, [])

    # Build A→C (left case)
    imp_left = Implies(left_and, eq_hn_ska)
    left_ctx = [f for f in got_left.sequent.left if not same(f, left_and)]
    got_imp_left = Proof(Sequent(left_ctx, [imp_left]),
        'implies_right', [got_left], principal=imp_left)

    # Build B→C (right case)
    imp_right = Implies(right_and, eq_hn_ska)
    right_ctx = [f for f in got_right_case.sequent.left if not same(f, right_and)]
    got_imp_right = Proof(Sequent(right_ctx, [imp_right]),
        'implies_right', [got_right_case], principal=imp_right)

    # Apply or_elim: HeadMove → (A→C) → (B→C) → C
    got_result = apply_thm(oe, [], hm,
        Implies(imp_left, Implies(imp_right, eq_hn_ska)), ax(hm))
    got_result = mp(got_result, got_imp_left, imp_left, Implies(imp_right, eq_hn_ska))
    got_result = mp(got_result, got_imp_right, imp_right, eq_hn_ska)

    # Close
    for premise in [succ_ska, num_d1, eq_d_d1, eq_h_ka, hm]:
        imp = Implies(premise, got_result.sequent.right[0])
        left = [f for f in got_result.sequent.left if not same(f, premise)]
        got_result = Proof(Sequent(left, [imp]), 'implies_right', [got_result], principal=imp)

    proof = got_result
    for v in [d1, ska, ka, d, hn, h]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'headmove_right_elim'
    return proof


def func_eq_transfer():
    """Transfer Function across Eq.
    |- ∀f,g. Eq(f,g) → Function(f) → Function(g)

    Function = And(Relation, SingleValued). Both use In(p,f).
    Eq(f,g) = ∀p. p∈f ↔ p∈g. Transfer each In occurrence."""
    from tactics import apply_thm, mp, ax, wl, fl, eir, eel, cut
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_mp, iff_mp_rev)
    from core.proof import Proof, Sequent, same
    from theorems.tm import apply_func_transfer
    from vocab.functions import Function as FuncDef, Apply
    from vocab import Relation
    from core.proof import Proof, Sequent
    from core.derived import Exists

    f, g = Var(postfix='ff'), Var(postfix='fg')
    eq_fg = Eq(f, g)
    func_f = FuncDef(f)
    func_g = FuncDef(g)

    # Function(f) = And(Relation(f), single_valued(f))
    # Relation(f) = ∀p. In(p,f) → ∃x,y. OrdPair(p,x,y)
    # single_valued(f) = ∀x,y1,y2. And(Apply(f,x,y1), Apply(f,x,y2)) → Eq(y1,y2)
    #
    # For Relation(g): need ∀p. In(p,g) → ∃x,y.OrdPair(p,x,y).
    # From Relation(f): In(p,f) → ∃x,y.OrdPair(p,x,y).
    # Eq(f,g): In(p,g) → In(p,f) (backward). Chain: In(p,g) → In(p,f) → ∃x,y.OrdPair(p,x,y).
    #
    # For single_valued(g): ∀x,y1,y2. And(Apply(g,x,y1),Apply(g,x,y2)) → Eq(y1,y2).
    # apply_func_transfer: Eq(g,f) → Apply(g,x,y) → Apply(f,x,y).
    # So And(Apply(g,x,y1),Apply(g,x,y2)) → And(Apply(f,x,y1),Apply(f,x,y2)) → Eq(y1,y2).

    # This is doable but requires expanding Function, extracting conjuncts, transferring each,
    # and rebuilding. ~40 lines. Let me be mechanical.

    # Strategy: build Function(g) from Function(f) + Eq(f,g).
    # Function(g) = And(Relation(g), sv(g)).
    # Function(f) = And(Relation(f), sv(f)). Extract both.

    rel_f = Relation(f)
    rel_g = Relation(g)

    # Extract Relation(f) from Function(f):
    func_exp = func_f.expand()  # And(Relation(f), sv(f))
    sv_f_form = func_exp.right  # the single_valued part
    got_rel_f = apply_thm(and_elim_left(rel_f, sv_f_form, []), [],
        func_f, rel_f, ax(func_f))
    got_sv_f = apply_thm(and_elim_right(rel_f, sv_f_form, []), [],
        func_f, sv_f_form, ax(func_f))

    # Build Relation(g): ∀p. In(p,g) → ∃x,y.OrdPair(p,x,y)
    # Relation(f): ∀p. In(p,f) → ∃x,y.OrdPair(p,x,y)
    # In(p,g) → In(p,f): from Eq(f,g) = ∀p. p∈f ↔ p∈g. Backward: p∈g → p∈f.
    # Actually Eq(f,g) = ∀z. z∈f ↔ z∈g. Forward: z∈f → z∈g. Backward: z∈g → z∈f.
    pv = Var(postfix='pv')
    in_pf = In(pv, f)
    in_pg = In(pv, g)
    iff_in = Iff(in_pf, in_pg)
    got_iff = apply_thm(ax(eq_fg), [pv], concl=iff_in)
    # [Eq(f,g)] |- Iff(In(pv,f), In(pv,g))
    got_back = apply_thm(iff_mp_rev(in_pf, in_pg, []), [],
        iff_in, Implies(in_pg, in_pf), got_iff)
    got_in_pf = mp(got_back, ax(in_pg), in_pg, in_pf)
    # [Eq(f,g), In(pv,g)] |- In(pv,f)

    # Relation(f) instantiated with pv: In(pv,f) → ∃x,y.OrdPair(pv,x,y)
    xv, yv = Var(postfix='xv'), Var(postfix='yv')
    rel_f_body = Exists(xv, Exists(yv, OrdPair(pv, xv, yv)))
    got_rel_inst = apply_thm(got_rel_f, [pv], in_pf, rel_f_body, got_in_pf)
    # [Function(f), Eq(f,g), In(pv,g)] |- ∃x,y.OrdPair(pv,x,y)

    # Close: In(pv,g) → ..., ∀pv
    imp_rel = Implies(in_pg, rel_f_body)
    got_rel_g = Proof(Sequent(
        [ff for ff in got_rel_inst.sequent.left if not same(ff, in_pg)],
        [imp_rel]), 'implies_right', [got_rel_inst], principal=imp_rel)
    fa_rel = Forall(pv, imp_rel)
    got_rel_g = Proof(Sequent(got_rel_g.sequent.left, [fa_rel]),
        'forall_right', [got_rel_g], principal=fa_rel, term=pv)
    # [Function(f), Eq(f,g)] |- Relation(g)

    # Build single_valued(g):
    # sv(f) = ∀x,y1,y2. And(Apply(f,x,y1),Apply(f,x,y2)) → Eq(y1,y2)
    # We need sv(g) = ∀x,y1,y2. And(Apply(g,x,y1),Apply(g,x,y2)) → Eq(y1,y2)
    # From Apply(g,x,y) → Apply(f,x,y) via apply_func_transfer + Eq(g,f):
    from theorems.logic import eq_symmetric
    es = eq_symmetric()
    eq_gf = Eq(g, f)
    got_eq_gf = apply_thm(es, [f, g], eq_fg, eq_gf, ax(eq_fg))

    aft = apply_func_transfer()
    x, y1, y2 = Var(postfix='svx'), Var(postfix='svy1'), Var(postfix='svy2')
    app_gx1 = Apply(g, x, y1)
    app_gx2 = Apply(g, x, y2)
    app_fx1 = Apply(f, x, y1)
    app_fx2 = Apply(f, x, y2)
    eq_y12 = Eq(y1, y2)

    # Apply(g,x,y1) → Apply(f,x,y1)
    got_fx1 = mp(apply_thm(aft, [g, f, x, y1], eq_gf,
        Implies(app_gx1, app_fx1), got_eq_gf), ax(app_gx1), app_gx1, app_fx1)
    got_fx2 = mp(apply_thm(aft, [g, f, x, y2], eq_gf,
        Implies(app_gx2, app_fx2), got_eq_gf), ax(app_gx2), app_gx2, app_fx2)

    # And(Apply(f,x,y1), Apply(f,x,y2)):
    ai = and_intro(app_fx1, app_fx2, [])
    got_and_f = mp(apply_thm(ai, [], app_fx1, Implies(app_fx2, And(app_fx1, app_fx2)), got_fx1),
        got_fx2, app_fx2, And(app_fx1, app_fx2))

    # sv(f) instantiated: And(Apply(f,x,y1),Apply(f,x,y2)) → Eq(y1,y2)
    got_sv_inst = apply_thm(got_sv_f, [x, y1, y2], And(app_fx1, app_fx2), eq_y12, got_and_f)
    # [Function(f), Eq(f,g), Apply(g,x,y1), Apply(g,x,y2)] |- Eq(y1,y2)

    # Build And(Apply(g,x,y1), Apply(g,x,y2)) on left, discharge
    and_gx = And(app_gx1, app_gx2)
    got_gx1 = apply_thm(and_elim_left(app_gx1, app_gx2, []), [], and_gx, app_gx1, ax(and_gx))
    got_gx2 = apply_thm(and_elim_right(app_gx1, app_gx2, []), [], and_gx, app_gx2, ax(and_gx))
    got_sv_g = cut(got_sv_inst, app_gx1, got_gx1)
    got_sv_g = cut(got_sv_g, app_gx2, got_gx2)
    # [Function(f), Eq(f,g), And(Apply(g,x,y1),Apply(g,x,y2))] |- Eq(y1,y2)

    imp_sv = Implies(and_gx, eq_y12)
    got_sv_g = Proof(Sequent([ff for ff in got_sv_g.sequent.left if not same(ff, and_gx)],
        [imp_sv]), 'implies_right', [got_sv_g], principal=imp_sv)
    for v in [y2, y1, x]:
        body = got_sv_g.sequent.right[0]
        fa = Forall(v, body)
        got_sv_g = Proof(Sequent(got_sv_g.sequent.left, [fa]),
            'forall_right', [got_sv_g], principal=fa, term=v)
    # [Function(f), Eq(f,g)] |- sv(g)

    # And(Relation(g), sv(g)) = Function(g)
    ai2 = and_intro(rel_g, got_sv_g.sequent.right[0], [])
    got_func_g = mp(apply_thm(ai2, [], rel_g,
        Implies(got_sv_g.sequent.right[0], func_g), got_rel_g),
        got_sv_g, got_sv_g.sequent.right[0], func_g)

    # Close
    for premise in [func_f, eq_fg]:
        imp = Implies(premise, got_func_g.sequent.right[0])
        left = [ff for ff in got_func_g.sequent.left if not same(ff, premise)]
        got_func_g = Proof(Sequent(left, [imp]), 'implies_right', [got_func_g], principal=imp)

    proof = got_func_g
    for v in [g, f]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'func_eq_transfer'
    return proof


_PHASE1_STEP_TMSTEP_OLD = """
    # === Part 2: Prove TMStep(delta, ca, ca_new) ===
    # TMStep = ∀q,h,tape,sym,w,d,qn,hn,tapen.
    #   Config(ca,q,h,tape) → Apply(tape,h,sym) → Trans(delta,q,sym,w,d,qn) →
    #   TapeUpdate(tapen,tape,h,w) → HeadMove(h,hn,d) → Config(ca_new,qn,hn,tapen)

    # Fresh vars for the 9 universally quantified
    q = Var(postfix='sq')
    h = Var(postfix='sh')
    tape = Var(postfix='st')
    sym = Var(postfix='ss')
    w = Var(postfix='sw')
    d = Var(postfix='sd')
    qn = Var(postfix='sqn')
    hn = Var(postfix='shn')
    tapen = Var(postfix='stn')

    # The 5 premises (will be assumed on left, then discharged)
    p_cfg = TMConfig(ca, q, h, tape)
    p_read = Apply(tape, h, sym)
    p_trans = TMTransition(delta, q, sym, w, d, qn)
    p_upd = TapeUpdate(tapen, tape, h, w)
    p_move = HeadMove(h, hn, d)
    # The conclusion
    p_goal = TMConfig(ca_new, qn, hn, tapen)

    # --- Step A: Config decomposition → Eq(q,q0), Eq(h,ka), Eq(tape,tape_in) ---

    # ordpair_exists(h, tape) → ∃v0. OrdPair(v0, h, tape)
    v0 = Var(postfix='v0')
    op_v0 = OrdPair(v0, h, tape)
    got_ex_v0 = apply_thm(oe, [h, tape], concl=Exists(v0, op_v0))

    # Config(ca, q, h, tape) instantiated with v0:
    #   OrdPair(v0,h,tape) → OrdPair(ca,q,v0)
    op_ca_q_v0 = OrdPair(ca, q, v0)
    got_cfg_inst = apply_thm(ax(p_cfg), [v0], op_v0, op_ca_q_v0, ax(op_v0))
    # [p_cfg, OrdPair(v0,h,tape)] |- OrdPair(ca, q, v0)

    # We need OrdPair(ca, q0, inner_ca) for ca's known decomposition.
    # ca was constructed with specific inner. We have the OrdPair facts from
    # the construction context. For this proof, we need them as hypotheses.
    # Actually, TMConfig(ca, q0, ka, tape_in) IS our hypothesis. Instantiate it too.
    inner_ca = Var(postfix='ica')
    op_inner_ca = OrdPair(inner_ca, ka, tape_in)
    op_ca_known = OrdPair(ca, q0, inner_ca)
    got_ex_ica = apply_thm(oe, [ka, tape_in], concl=Exists(inner_ca, op_inner_ca))

    # From cfg_ca = TMConfig(ca,q0,ka,tape_in), instantiate with inner_ca:
    got_ca_known = apply_thm(ax(cfg_ca), [inner_ca], op_inner_ca, op_ca_known, ax(op_inner_ca))
    # [cfg_ca, OrdPair(inner_ca,ka,tape_in)] |- OrdPair(ca, q0, inner_ca)

    # tuple_injection on OrdPair(ca,q,v0) and OrdPair(ca,q0,inner_ca)
    ti = tuple_injection()
    eq_q_q0 = Eq(q, q0)
    eq_v0_ica = Eq(v0, inner_ca)
    and_eq1 = And(eq_q_q0, eq_v0_ica)
    got_ti1 = apply_thm(ti, [q, v0, q0, inner_ca, ca])
    got_ti1 = mp(got_ti1, got_cfg_inst, op_ca_q_v0,
        Implies(op_ca_known, and_eq1))
    got_ti1 = mp(got_ti1, got_ca_known, op_ca_known, and_eq1)
    # [Pairing, p_cfg, op_v0, cfg_ca, op_inner_ca] |- And(Eq(q,q0), Eq(v0,inner_ca))

    ael = and_elim_left(eq_q_q0, eq_v0_ica, [])
    aer = and_elim_right(eq_q_q0, eq_v0_ica, [])
    got_eq_q = apply_thm(ael, [], and_eq1, eq_q_q0, got_ti1)
    got_eq_v0 = apply_thm(aer, [], and_eq1, eq_v0_ica, got_ti1)

    # Transfer OrdPair(v0,h,tape) to OrdPair(inner_ca,h,tape) via Eq(v0,inner_ca)
    ost = ordpair_set_transfer()
    es = eq_symmetric()
    eq_ica_v0 = Eq(inner_ca, v0)
    got_eq_ica_v0 = apply_thm(es, [v0, inner_ca], eq_v0_ica, eq_ica_v0, got_eq_v0)
    got_op_ica_ht = mp(apply_thm(ost, [inner_ca, v0, h, tape], eq_ica_v0,
        Implies(op_v0, OrdPair(inner_ca, h, tape)), got_eq_ica_v0),
        ax(op_v0), op_v0, OrdPair(inner_ca, h, tape))

    # tuple_injection on OrdPair(inner_ca,h,tape) and OrdPair(inner_ca,ka,tape_in)
    eq_h_ka = Eq(h, ka)
    eq_t_tin = Eq(tape, tape_in)
    and_eq2 = And(eq_h_ka, eq_t_tin)
    got_ti2 = apply_thm(ti, [h, tape, ka, tape_in, inner_ca])
    got_ti2 = mp(got_ti2, got_op_ica_ht, OrdPair(inner_ca, h, tape),
        Implies(op_inner_ca, and_eq2))
    got_ti2 = mp(got_ti2, ax(op_inner_ca), op_inner_ca, and_eq2)

    got_eq_h = apply_thm(and_elim_left(eq_h_ka, eq_t_tin, []), [],
        and_eq2, eq_h_ka, got_ti2)
    got_eq_t = apply_thm(and_elim_right(eq_h_ka, eq_t_tin, []), [],
        and_eq2, eq_t_tin, got_ti2)

    # Eliminate v0 and inner_ca existentials
    def elim_var(proof, formula, var, ex_proof):
        p = eel(proof, formula, var)
        return cut(p, Exists(var, formula), ex_proof)

    for p_ref in ['got_eq_q', 'got_eq_h', 'got_eq_t']:
        locals()[p_ref] = elim_var(locals()[p_ref], op_v0, v0, got_ex_v0)
        locals()[p_ref] = elim_var(locals()[p_ref], op_inner_ca, inner_ca, got_ex_ica)
    got_eq_q = locals()['got_eq_q']
    got_eq_h = locals()['got_eq_h']
    got_eq_t = locals()['got_eq_t']
    # [Pairing, p_cfg, cfg_ca] |- Eq(q,q0), Eq(h,ka), Eq(tape,tape_in)

    # --- Step B: Eq(sym, one) from Apply + Function ---
    # Apply(tape,h,sym) → transfer to Apply(tape_in,ka,sym) → func_unique with Apply(tape_in,ka,one)
    eat = eq_apply_transfer()
    # Transfer h→ka: Apply(tape,h,sym) → Apply(tape,ka,sym)
    got_app_ka = mp(apply_thm(eat, [tape, h, ka, sym], eq_h_ka,
        Implies(p_read, Apply(tape, ka, sym)), got_eq_h),
        ax(p_read), p_read, Apply(tape, ka, sym))

    # Transfer tape→tape_in: Apply(tape,ka,sym) → Apply(tape_in,ka,sym)
    # eq_apply_transfer transfers the first arg of Apply. For the function position,
    # we need: Eq(tape, tape_in) → Apply(tape, ka, sym) → Apply(tape_in, ka, sym).
    # This requires transferring the function position. Use eq_substitution on In.
    # Apply(f,x,y) = ∃p. OrdPair(p,x,y) ∧ In(p,f). Eq(f,g) → In(p,f) ↔ In(p,g).
    # So Apply(tape,ka,sym) → Apply(tape_in,ka,sym) via Eq(tape,tape_in).
    # This is complex inline. Let me use func_unique differently.

    # Actually simpler: we have Eq(tape, tape_in). Function(tape_in) on left.
    # We can derive Function(tape) from Eq(tape, tape_in) + Function(tape_in).
    # Then func_unique(tape, h, sym, ???). But we need two Apply's on the same tape.
    # We have Apply(tape, h, sym) and need to connect to Apply(tape_in, ka, one).
    # With Eq(tape,tape_in) and Eq(h,ka): the Apply facts are about DIFFERENT tapes/positions.

    # Better: transfer Apply(tape_in,ka,one) to Apply(tape,h,one) using reverse Eq's.
    # Eq(h,ka) → eq_symmetric → Eq(ka,h) → eq_apply_transfer → Apply(tape_in,h,one) from Apply(tape_in,ka,one).
    # Eq(tape,tape_in) → eq_symmetric → Eq(tape_in,tape) → function-transfer → Apply(tape,h,one).
    # But function-position transfer is still complex.

    # Simplest approach: use func_unique on tape_in with Apply(tape_in,ka,sym) and Apply(tape_in,ka,one).
    # But we need Apply(tape_in,ka,sym) which requires tape→tape_in transfer.

    # Let me just build Apply(tape_in,ka,sym) from Apply(tape,h,sym) + Eq(h,ka) + Eq(tape,tape_in).
    # Step 1: Apply(tape,h,sym) → Apply(tape,ka,sym) via eq_apply_transfer + Eq(h,ka). Done above.
    # Step 2: Apply(tape,ka,sym) → need In(p,tape) → In(p,tape_in) transfer.
    # Apply(tape,ka,sym) = ∃p. OrdPair(p,ka,sym) ∧ In(p,tape).
    # Eq(tape,tape_in) via eq_substitution → In(p,tape) ↔ In(p,tape_in).
    # So ∃p. OrdPair(p,ka,sym) ∧ In(p,tape_in) = Apply(tape_in,ka,sym).

    # This is the eq_apply_func_transfer pattern. Let me inline it.
    pv = Var(postfix='pv')
    op_pv = OrdPair(pv, ka, sym)
    in_pv_tape = In(pv, tape)
    in_pv_tin = In(pv, tape_in)
    and_pv = And(op_pv, in_pv_tape)

    # eq_substitution: Eq(tape,tape_in) → Iff(In(pv,tape), In(pv,tape_in))
    eqs = eq_substitution()
    iff_in = Iff(in_pv_tape, in_pv_tin)
    got_iff_in = apply_thm(eqs, [tape, tape_in, pv])
    got_iff_in = mp(got_iff_in, got_eq_t, eq_t_tin, iff_in)
    # [...] |- Iff(In(pv,tape), In(pv,tape_in))

    got_fwd_in = apply_thm(iff_mp(in_pv_tape, in_pv_tin, []), [],
        iff_in, Implies(in_pv_tape, in_pv_tin), got_iff_in)
    # [...] |- In(pv,tape) → In(pv,tape_in)

    # From Apply(tape,ka,sym) = ∃pv. And(OrdPair(pv,ka,sym), In(pv,tape)):
    # Extract, transfer In, rebuild.
    got_in_tin = mp(got_fwd_in, ax(in_pv_tape), in_pv_tape, in_pv_tin)
    # [..., In(pv,tape)] |- In(pv,tape_in)
    ai_new = and_intro(op_pv, in_pv_tin, [])
    got_and_new = mp(apply_thm(ai_new, [], op_pv,
        Implies(in_pv_tin, And(op_pv, in_pv_tin)), ax(op_pv)),
        got_in_tin, in_pv_tin, And(op_pv, in_pv_tin))
    got_app_tin_sym = eir(got_and_new, And(op_pv, in_pv_tin), pv, pv)
    # [..., OrdPair(pv,ka,sym), In(pv,tape)] |- Apply(tape_in, ka, sym)

    # Merge OrdPair+In into And, eel pv
    got_op_from = apply_thm(and_elim_left(op_pv, in_pv_tape, []), [],
        and_pv, op_pv, ax(and_pv))
    got_in_from = apply_thm(and_elim_right(op_pv, in_pv_tape, []), [],
        and_pv, in_pv_tape, ax(and_pv))
    got_app_tin_sym = cut(got_app_tin_sym, op_pv, got_op_from)
    got_app_tin_sym = cut(got_app_tin_sym, in_pv_tape, got_in_from)
    got_app_tin_sym = eel(got_app_tin_sym, and_pv, pv)
    # [..., Apply(tape,ka,sym)] |- Apply(tape_in, ka, sym)

    # Replace Apply(tape,ka,sym) with got_app_ka via cut
    got_app_tin_sym = cut(got_app_tin_sym, Apply(tape, ka, sym), got_app_ka)
    # [..., p_read, Eq(h,ka), Eq(tape,tape_in), Extensionality] |- Apply(tape_in, ka, sym)

    # func_unique: Function(tape_in) → Apply(tape_in,ka,sym) → Apply(tape_in,ka,one) → Eq(sym,one)
    fu = func_unique_thm()
    eq_sym_one = Eq(sym, one)
    got_fu = apply_thm(fu, [tape_in, ka, sym, one])
    got_fu = mp(got_fu, ax(func_tape), func_tape, got_fu.sequent.right[0].right)
    got_fu = mp(got_fu, got_app_tin_sym, Apply(tape_in, ka, sym),
        got_fu.sequent.right[0].right)
    got_fu = mp(got_fu, ax(app_tape_ka), app_tape_ka, eq_sym_one)
    got_eq_sym = got_fu
    # [...] |- Eq(sym, one)

    # --- Step C: Function(delta) → Eq(w,one), Eq(d,d1), Eq(qn,q0) ---
    # TMTransition(delta,q,sym,w,d,qn) instantiated with inp_pair gives Apply(delta,inp,out).
    # TMTransition(delta,q0,one,one,d1,q0) instantiated with same inp gives Apply(delta,inp,out_known).
    # Function(delta) → Eq(out, out_known) → pair injection → Eq's on components.

    # Build inp = (q, sym) and inp_known = (q0, one).
    # With Eq(q,q0) and Eq(sym,one): ordpair_eq_transfer → OrdPair(inp,q0,one) from OrdPair(inp,q,sym).
    # Then ordpair_unique → Eq(inp, inp_known).
    inp = Var(postfix='inp')
    op_inp = OrdPair(inp, q, sym)
    got_ex_inp = apply_thm(oe, [q, sym], concl=Exists(inp, op_inp))

    # Transfer OrdPair(inp,q,sym) to OrdPair(inp,q0,one) via Eq(q,q0), Eq(sym,one)
    oet = ordpair_eq_transfer()
    op_inp_known = OrdPair(inp, q0, one)
    got_inp_known = apply_thm(oet, [q, sym, q0, one, inp])
    got_inp_known = mp(got_inp_known, got_eq_q, eq_q_q0, got_inp_known.sequent.right[0].right)
    got_inp_known = mp(got_inp_known, got_eq_sym, eq_sym_one, got_inp_known.sequent.right[0].right)
    got_inp_known = mp(got_inp_known, ax(op_inp), op_inp, op_inp_known)
    # [..., OrdPair(inp,q,sym)] |- OrdPair(inp, q0, one)

    # Build output pairs for both transitions.
    # p_trans: TMTransition(delta,q,sym,w,d,qn)
    #   instantiate with inp → ∀dp. OrdPair(dp,d,qn) → ∀out. OrdPair(out,w,dp) → Apply(delta,inp,out)
    # trans_known: TMTransition(delta,q0,one,one,d1,q0)
    #   instantiate with inp → ∀dp. OrdPair(dp,d1,q0) → ∀out. OrdPair(out,one,dp) → Apply(delta,inp,out)

    dp1 = Var(postfix='dp1')
    out1 = Var(postfix='out1')
    op_dp1 = OrdPair(dp1, d, qn)
    op_out1 = OrdPair(out1, w, dp1)
    app_d1 = Apply(delta, inp, out1)

    got_ex_dp1 = apply_thm(oe, [d, qn], concl=Exists(dp1, op_dp1))
    got_ex_out1 = apply_thm(oe, [w, dp1], concl=Exists(out1, op_out1))

    # Instantiate p_trans with inp, dp1, out1:
    got_trans1 = apply_thm(ax(p_trans), [inp], op_inp,
        Forall(dp1, Implies(op_dp1, Forall(out1, Implies(op_out1, app_d1)))),
        ax(op_inp))
    got_trans1 = apply_thm(got_trans1, [dp1], op_dp1,
        Forall(out1, Implies(op_out1, app_d1)), ax(op_dp1))
    got_trans1 = apply_thm(got_trans1, [out1], op_out1, app_d1, ax(op_out1))
    # [p_trans, OrdPair(inp,q,sym), OrdPair(dp1,d,qn), OrdPair(out1,w,dp1)] |- Apply(delta,inp,out1)

    # Similarly for trans_known with inp, dp2, out2:
    dp2 = Var(postfix='dp2')
    out2 = Var(postfix='out2')
    op_dp2 = OrdPair(dp2, d1, q0)
    op_out2 = OrdPair(out2, one, dp2)
    app_d2 = Apply(delta, inp, out2)

    got_ex_dp2 = apply_thm(oe, [d1, q0], concl=Exists(dp2, op_dp2))
    got_ex_out2 = apply_thm(oe, [one, dp2], concl=Exists(out2, op_out2))

    got_trans2 = apply_thm(ax(trans_known), [inp])
    got_trans2 = apply_thm(got_trans2, [dp2])
    while type(got_trans2.sequent.right[0]).__name__ == 'Implies':
        cur = got_trans2.sequent.right[0]
        got_trans2 = mp(got_trans2, ax(cur.left), cur.left, cur.right)
    # [trans_known, OrdPair(inp,q0,one), OrdPair(dp2,d1,q0), OrdPair(out2,one,dp2)] |- Apply(delta,inp,out2)

    # Transfer OrdPair(inp,q0,one) via got_inp_known:
    got_trans2 = cut(got_trans2, OrdPair(inp, q0, one), got_inp_known)

    # func_unique on delta: Apply(delta,inp,out1) ∧ Apply(delta,inp,out2) → Eq(out1,out2)
    eq_out = Eq(out1, out2)
    got_fu_d = apply_thm(fu, [delta, inp, out1, out2])
    got_fu_d = mp(got_fu_d, ax(func_delta), func_delta, got_fu_d.sequent.right[0].right)
    got_fu_d = mp(got_fu_d, got_trans1, app_d1, got_fu_d.sequent.right[0].right)
    got_fu_d = mp(got_fu_d, got_trans2, app_d2, eq_out)
    # [...] |- Eq(out1, out2)

    # tuple_injection on OrdPair(out1,w,dp1) and OrdPair(out2,one,dp2):
    # First transfer: OrdPair(out2,...) → OrdPair(out1,...) via Eq(out1,out2)
    # Actually: tuple_injection needs OrdPair(t,a,b) ∧ OrdPair(t,c,d).
    # Transfer out2 to out1: ordpair_set_transfer + Eq(out1,out2)
    eq_out_sym = Eq(out2, out1)
    got_eq_out_sym = apply_thm(es, [out1, out2], eq_out, eq_out_sym, got_fu_d)
    op_out1_from2 = OrdPair(out1, one, dp2)
    got_op_out1_2 = mp(apply_thm(ost, [out1, out2, one, dp2], eq_out_sym,
        Implies(op_out2, op_out1_from2), got_eq_out_sym),
        ax(op_out2), op_out2, op_out1_from2)
    # [..., OrdPair(out2,one,dp2)] |- OrdPair(out1, one, dp2)

    eq_w_one = Eq(w, one)
    eq_dp1_dp2 = Eq(dp1, dp2)
    and_eq3 = And(eq_w_one, eq_dp1_dp2)
    got_ti3 = apply_thm(ti, [w, dp1, one, dp2, out1])
    got_ti3 = mp(got_ti3, ax(op_out1), op_out1, Implies(op_out1_from2, and_eq3))
    got_ti3 = mp(got_ti3, got_op_out1_2, op_out1_from2, and_eq3)
    got_eq_w = apply_thm(and_elim_left(eq_w_one, eq_dp1_dp2, []), [],
        and_eq3, eq_w_one, got_ti3)
    got_eq_dp = apply_thm(and_elim_right(eq_w_one, eq_dp1_dp2, []), [],
        and_eq3, eq_dp1_dp2, got_ti3)

    # Similarly: tuple_injection on OrdPair(dp1,d,qn) and OrdPair(dp2,d1,q0)
    # Transfer dp2→dp1 via Eq(dp1,dp2)
    eq_dp_sym = Eq(dp2, dp1)
    got_eq_dp_sym = apply_thm(es, [dp1, dp2], eq_dp1_dp2, eq_dp_sym, got_eq_dp)
    op_dp1_from2 = OrdPair(dp1, d1, q0)
    got_op_dp1_2 = mp(apply_thm(ost, [dp1, dp2, d1, q0], eq_dp_sym,
        Implies(op_dp2, op_dp1_from2), got_eq_dp_sym),
        ax(op_dp2), op_dp2, op_dp1_from2)

    eq_d_d1 = Eq(d, d1)
    eq_qn_q0 = Eq(qn, q0)
    and_eq4 = And(eq_d_d1, eq_qn_q0)
    got_ti4 = apply_thm(ti, [d, qn, d1, q0, dp1])
    got_ti4 = mp(got_ti4, ax(op_dp1), op_dp1, Implies(op_dp1_from2, and_eq4))
    got_ti4 = mp(got_ti4, got_op_dp1_2, op_dp1_from2, and_eq4)
    got_eq_d = apply_thm(and_elim_left(eq_d_d1, eq_qn_q0, []), [],
        and_eq4, eq_d_d1, got_ti4)
    got_eq_qn = apply_thm(and_elim_right(eq_d_d1, eq_qn_q0, []), [],
        and_eq4, eq_qn_q0, got_ti4)

    # Eliminate existential vars: inp, dp1, out1, dp2, out2
    for vname in ['got_eq_w', 'got_eq_d', 'got_eq_qn']:
        p = locals()[vname]
        for var, formula, ex_p in [
            (out2, op_out2, got_ex_out2), (dp2, op_dp2, got_ex_dp2),
            (out1, op_out1, got_ex_out1), (dp1, op_dp1, got_ex_dp1),
            (inp, op_inp, got_ex_inp)]:
            if any(same(formula, f) for f in p.sequent.left):
                p = elim_var(p, formula, var, ex_p)
        locals()[vname] = p
    got_eq_w = locals()['got_eq_w']
    got_eq_d = locals()['got_eq_d']
    got_eq_qn = locals()['got_eq_qn']

    # --- Step D: HeadMove → Eq(hn, ska) ---
    # HeadMove(h,hn,d) = Or(And(Num(d,1),Succ(hn,h)), And(Num(d,0),Succ(h,hn)))
    # We have Eq(h,ka), Eq(d,d1), Num(d1,1), Successor(ska,ka).
    # In left case: Num(d,1) ∧ Succ(hn,h). Transfer h→ka: Succ(hn,ka).
    #   unique_successor + Succ(ska,ka) → Eq(hn,ska).
    # In right case: Num(d,0). But Eq(d,d1) + Num(d1,1) → Num(d,1).
    #   Num(d,0) ∧ Num(d,1): d=∅ and d=S(∅). succ_not_empty → contradiction.
    # Result: Eq(hn, ska) from or_elim.

    # This is complex enough to warrant its own sub-proof.
    # For now, build it inline.

    # Left case: And(Num(d,1), Succ(hn,h)) → Eq(hn,ska)
    from theorems.sets import unique_successor
    us = unique_successor()
    # unique_successor: ∀a,b,c. Succ(b,a) → Succ(c,a) → Eq(b,c)
    succ_hn_h = Successor(hn, h)
    succ_hn_ka = Successor(hn, ka)
    eq_hn_ska = Eq(hn, ska)
    left_and_hm = And(Num(d, 1), succ_hn_h)

    # From left_and: extract Succ(hn,h)
    got_succ_hnh = apply_thm(and_elim_right(Num(d,1), succ_hn_h, []), [],
        left_and_hm, succ_hn_h, ax(left_and_hm))

    # Transfer Succ(hn,h) to Succ(hn,ka) via Eq(h,ka): ordpair_val_transfer
    ovt = ordpair_val_transfer()
    got_succ_hnka = mp(apply_thm(ovt, [hn, h, ka], eq_h_ka,  # Eq(h,ka) not Eq(ka,h)... check direction
        Implies(succ_hn_h, succ_hn_ka), got_eq_h),
        got_succ_hnh, succ_hn_h, succ_hn_ka)

    # unique_successor: Succ(hn,ka) → Succ(ska,ka) → Eq(hn,ska)
    got_eq_hn_left = mp(apply_thm(us, [ka, hn, ska], succ_hn_ka,
        Implies(succ_ska, eq_hn_ska), got_succ_hnka),
        ax(succ_ska), succ_ska, eq_hn_ska)
    # [..., left_and_hm, Eq(h,ka), Succ(ska,ka)] |- Eq(hn,ska)

    # Right case: And(Num(d,0), Succ(h,hn)) → contradiction → Eq(hn,ska)
    right_and_hm = And(Num(d, 0), Successor(h, hn))
    got_numd0 = apply_thm(and_elim_left(Num(d,0), Successor(h,hn), []), [],
        right_and_hm, Num(d,0), ax(right_and_hm))
    # [right_and_hm] |- Num(d,0) = Empty(d)

    # Eq(d,d1) + Num(d1,1): transfer Num(d1,1) to Num(d,1) via eq_symmetric
    # Num(d1,1) = Successor(d1, some_zero). Eq(d,d1) → Successor(d, some_zero) = Num(d,1)?
    # Actually Num(x, 1) = Successor(x, some_zero) where Num(some_zero, 0) = Empty(some_zero).
    # More precisely, Num(d1, 1) expands to a specific formula. We can transfer
    # via: Eq(d, d1) → (z ∈ d ↔ z ∈ d1) → Num(d, 1) ↔ Num(d1, 1).
    # Since Num is defined via In/Eq patterns, Eq(d,d1) propagates.
    # Actually Num(d,1) = Successor(d, ∅_var) where ∅_var satisfies Empty.
    # Successor(d, ∅_var) = ∀z. z∈d ↔ (z=∅_var ∨ z∈∅_var). Hmm, it's complex.
    # Simplest: use the fact that Num(d,0) means d=∅, Num(d1,1) means d1=S(∅).
    # Eq(d,d1): d=d1. But d=∅ and d1=S(∅) → ∅=S(∅) → contradicts succ_not_empty.

    # succ_not_empty: ∀x. ¬Empty(S(x)). Equivalently, S(x) ≠ ∅.
    # Eq(d, d1) + Empty(d) → Empty(d1).
    # But Num(d1, 1) = Successor(d1, something) → d1 is nonempty.
    # Actually, we can derive ¬Empty(d1) from Num(d1,1):
    # Num(d1,1): d1 = S(∅). succ_not_empty: ¬Empty(S(x)) for all x. So ¬Empty(d1).

    # eq_substitution: Eq(d,d1) → Iff(In(z,d), In(z,d1)) → Eq(d,d1) acts as d≡d1.
    # From Empty(d) = ∀z.¬In(z,d) and Eq(d,d1): ∀z.¬In(z,d1) = Empty(d1).
    # From Num(d1,1) via succ_not_empty: ¬Empty(d1). Contradiction.

    # This is getting very verbose. Let me use a shortcut: derive ⊥ from the right case
    # and weaken to get Eq(hn,ska).

    # From Empty(d) + Eq(d,d1): derive Empty(d1) via eq transfer.
    # Empty(d) = Forall(z, Not(In(z, d))). Transfer In(z,d) ↔ In(z,d1) via Eq(d,d1).
    # Then Forall(z, Not(In(z, d1))) = Empty(d1).
    # But I need ¬Empty(d1). From num_d1 = Num(d1,1):
    # Num(x,1) means x = S(∅). succ_not_empty says ¬Empty(S(y)) for all y.
    # With x = S(∅): ¬Empty(S(∅)). And S(∅) = d1. So ¬Empty(d1).
    # But proving ¬Empty(d1) from Num(d1,1) needs the succ_not_empty theorem + instantiation.

    # Actually, this is really verbose. For the right HeadMove case, the whole thing
    # is contradictory, so the implication is vacuously true. Let me just weaken ⊥
    # to Eq(hn,ska).
    #
    # I'll build: [right_and_hm, Eq(d,d1), Num(d1,1), ...] |- ⊥, then weaken.

    from theorems.sets import succ_not_empty
    sne = succ_not_empty()
    # succ_not_empty: ∀x. Not(Empty(Successor_set(x)))
    # Actually let me check what succ_not_empty proves exactly.
    # It should give us something about S(x) not being empty.
    # For now, let me just use a simpler approach: assume the right case
    # and derive ⊥, then weaken_right to get Eq(hn,ska).

    # The right case gives Num(d,0) = Empty(d). Eq(d,d1) means d≡d1.
    # Num(d1,1) means d1 = {∅, {∅}} or similar (nonempty).
    # The contradiction: Empty(d) + Eq(d,d1) + Num(d1,1).
    # Empty(d): ∀z. ¬In(z,d). Eq(d,d1): In(z,d) ↔ In(z,d1). So ∀z. ¬In(z,d1) = Empty(d1).
    # Num(d1,1) expands to Successor(d1, zero_val) for some zero_val with Empty(zero_val).
    # Successor(d1, zero_val) = ∀z. In(z,d1) ↔ Or(Eq(z,zero_val), In(z,zero_val)).
    # From Empty(d1): ¬In(z,d1) for all z. In particular, not In(zero_val, d1).
    # But Successor: In(zero_val, d1) ↔ Or(Eq(zero_val,zero_val), In(zero_val,zero_val)).
    # Eq(zero_val,zero_val) is true (eq_reflexive). So left disjunct of Or is true.
    # So In(zero_val,d1) should be true. Contradicts Empty(d1).

    # This is too many steps inline. Let me just weaken the right case to ⊥ → anything,
    # by leaving the right case as a TODO that produces Eq(hn,ska) from ⊥.
    # Actually, I can do it more simply:
    # [right_and_hm, context] |- ⊥ is hard to prove inline.
    # BUT: or_elim just needs left_case→C and right_case→C.
    # For the right case, I need [right_and_hm, context] |- Eq(hn,ska).
    # I can get this via: [right_and_hm, context] |- ⊥, then ⊥→Eq(hn,ska).
    # But proving ⊥ is the hard part.

    # SIMPLIFICATION: Instead of or_elim, I can prove Eq(hn,ska) from
    # HeadMove(h,hn,d) directly by case analysis on d=1 (true) vs d=0 (false).
    # Since Eq(d,d1) and Num(d1,1):
    # HeadMove = Or(And(Num(d,1), Succ(hn,h)), And(Num(d,0), Succ(h,hn)))
    #          = Implies(Not(And(Num(d,1), Succ(hn,h))), And(Num(d,0), Succ(h,hn)))
    # If we can prove And(Num(d,1), Succ(hn,h)):
    #   Then Not(And(Num(d,1), Succ(hn,h))) is false, so the Implies is irrelevant.
    #   But we don't have Succ(hn,h) — that's what we're trying to prove.

    # Actually, HeadMove IS an Or on the left. We ASSUME it as a premise.
    # or_elim gives us: from each disjunct, derive Eq(hn,ska).
    # Left disjunct: straightforward (done above as got_eq_hn_left).
    # Right disjunct: contradictory, so anything follows.

    # For the contradiction from right case:
    # Num(d,0) + Eq(d,d1) → Num(d1,0)? No — Eq doesn't propagate into Num directly.
    # Actually, Num(d,0) = Empty(d). Eq(d,d1) via eq_substitution: In(z,d) ↔ In(z,d1).
    # So ∀z. ¬In(z,d) → ∀z. ¬In(z,d1). = Empty(d1).
    # Num(d1,1) = Successor(d1, ...). succ_not_empty applied to d1.
    # Actually succ_not_empty says: ¬Empty(S(x)), not ¬Empty(d1). We'd need to know d1=S(x) for some x.

    # This is very involved. Let me just skip the right case for now by noting that
    # in practice, the right case never occurs (d=d1, Num(d1,1), so d≠0).
    # I'll leave a clean TODO and revisit.
    # For now, assume got_eq_hn is proved from HeadMove.

    # Actually, let me use a different approach. Instead of or_elim on HeadMove,
    # I'll use head_move_right which directly gives:
    # Num(d,1) → Successor(hn,h) → HeadMove(h,hn,d)
    # That's the CONSTRUCTION direction. I need the EXTRACTION direction.
    # head_move_right proves HeadMove, not extracts from it.

    # OK, let me just handle the right case quickly.
    # Right case: [And(Num(d,0), Succ(h,hn)), Eq(d,d1), Num(d1,1)] |- Eq(hn,ska)
    # From And: Num(d,0) i.e. Empty(d).
    # From Eq(d,d1) + Empty(d): show Empty(d1).
    # From Num(d1,1): d1 = S(zero_v) for some zero_v. In(zero_v, d1) holds.
    # From Empty(d1): ¬In(zero_v, d1). Contradiction → anything.

    # Inline: derive ¬In(x, d1) from Empty(d) + Eq(d,d1)
    xv = Var(postfix='xv')
    not_in_xd = Not(In(xv, d))
    got_not_in = fl(got_numd0, not_in_xd, xv)
    # [right_and_hm] |- ¬In(xv, d)

    # eq_substitution: Eq(d,d1) → Iff(In(xv,d), In(xv,d1))
    iff_ind = Iff(In(xv, d), In(xv, d1))
    got_iff_d = apply_thm(eqs, [d, d1, xv], eq_d_d1, iff_ind, got_eq_d)
    # Transfer: ¬In(xv,d) → ¬In(xv,d1) using Iff backward → forward contrapositive
    # Iff(A,B) + ¬A → ¬B (contrapositive of Iff backward direction B→A):
    # From Iff: B→A. Contrapositive: ¬A→¬B.
    # Prove: [¬In(xv,d), In(xv,d1)] |- ⊥
    #   From Iff backward: In(xv,d1) → In(xv,d).
    got_bwd = apply_thm(iff_mp_rev(In(xv,d), In(xv,d1), []), [],
        iff_ind, Implies(In(xv,d1), In(xv,d)), got_iff_d)
    got_in_d = mp(got_bwd, ax(In(xv,d1)), In(xv,d1), In(xv,d))
    # [..., In(xv,d1)] |- In(xv,d)
    # Contradiction with ¬In(xv,d):
    got_bot_d = Proof(Sequent(list(got_in_d.sequent.left) + [not_in_xd], []),
        'not_left', [got_in_d], principal=not_in_xd)
    # Cut not_in_xd with got_not_in:
    got_bot_d = cut(got_bot_d, not_in_xd, got_not_in)
    # [right_and_hm, ..., In(xv,d1)] |- ⊥

    # Now we need In(xv, d1) to be derivable from Num(d1,1).
    # Num(d1,1) = Successor(d1, zero_val) where Empty(zero_val).
    # Successor(d1, zero_val) = ∀z. In(z,d1) ↔ Or(Eq(z,zero_val), In(z,zero_val))
    # With z=zero_val: In(zero_val,d1) ↔ Or(Eq(zero_val,zero_val), In(zero_val,zero_val))
    # Eq(zero_val,zero_val) is true → left disjunct → In(zero_val,d1).

    # But Num(d1,1) is a definition that expands to a complex formula.
    # Let me use a simpler approach: Num(d1,1) expands and contains ∃zero_val...
    # Actually, Num(x, n) is defined in vocab/omega.py.

    # For the right-case contradiction, I just need one element of d1.
    # Num(d1, 1) says d1 = {∅} (the successor of ∅).
    # Actually, let me just weaken ⊥ to Eq(hn,ska) if I can get ⊥.
    # I have got_bot_d: [..., In(xv, d1)] |- ⊥
    # I need In(xv, d1) for some xv. From Num(d1,1) = Successor(d1, ∅):
    # d1 contains ∅ as an element. So In(∅, d1).

    # But I don't have a variable for ∅ here. The Num(d1,1) definition handles this
    # internally. This is getting too deep.

    # PRACTICAL DECISION: The right HeadMove case (d=0, left move) is contradictory
    # given d=d1 and Num(d1,1). But proving the contradiction is ~30 lines of
    # Num expansion + Successor + succ_not_empty. This is pure plumbing.
    # Let me leave a placeholder and come back to it.
    # For testing, I'll use weakening_right on ⊥ to get Eq(hn,ska).

    # Actually, I realize I can avoid all this by noting:
    # We have ¬In(xv, d1) for ALL xv (from got_bot_d pattern for any xv).
    # Close ∀xv: got_bot_d with In(xv,d1) on left, close forall:
    not_in_xd1 = Not(In(xv, d1))
    got_not_in_d1 = Proof(Sequent(
        [f for f in got_bot_d.sequent.left if not same(f, In(xv, d1))],
        [not_in_xd1]), 'not_right', [got_bot_d], principal=not_in_xd1)
    fa_not_in = Forall(xv, not_in_xd1)
    got_empty_d1 = Proof(Sequent(got_not_in_d1.sequent.left, [fa_not_in]),
        'forall_right', [got_not_in_d1], principal=fa_not_in, term=xv)
    # [..., right_and_hm, Eq(d,d1)] |- Empty(d1) = ∀xv. ¬In(xv, d1)

    # succ_not_empty: ∀x. ¬Empty(S(x))
    # Num(d1,1) = Successor(d1, zero_val) where... this is about the STRUCTURE of d1.
    # succ_not_empty proves ¬Empty(S(x)). We need to show d1 = S(something).
    # This requires expanding Num(d1,1) which is definition-heavy.

    # Actually, succ_not_empty gives: Pairing |- ∀x. ¬Empty(S(x)).
    # With Num(d1,1): d1 looks like S(∅). But Num doesn't directly give S(∅) = d1.
    # Num(d1, 1) is defined as the ordinal successor chain from ∅.
    # For Num(d1, 1): Successor(d1, zero) where Num(zero, 0) = Empty(zero).

    # Hmm, let me just check what Num expands to.

    # Actually, for the proof to work, I don't need to fully expand Num.
    # I just need: Num(d1, 1) → ¬Empty(d1).
    # This is: S(∅) is not empty. succ_not_empty gives ¬Empty(S(x)) for all x.
    # But I need to show d1 is a successor. Num(d1,1) = Successor(d1, y) ∧ Empty(y).
    # From Successor(d1, y): there exists an element in d1 (namely y ∈ d1 since y ∈ S(y)).
    # So ¬Empty(d1).

    # SIMPLEST: from Num(d1,1), extract ∃y. Successor(d1,y).
    # Successor(d1,y) = ∀z. In(z,d1) ↔ Or(Eq(z,y), In(z,y)).
    # Instantiate z=y: In(y,d1) ↔ Or(Eq(y,y), In(y,y)). Eq(y,y) is true.
    # So In(y,d1) is true. Combined with Empty(d1) = ¬In(y,d1). ⊥.

    # But extracting y from Num(d1,1) requires expanding the Num definition.
    # Num(d1,1) in vocab/omega.py... let me check.

    # I think the cleanest approach is to factor this out as a helper:
    # not_zero_one: Num(x,0) → Num(y,1) → ¬Eq(x,y)
    # or equivalently: Num(x,0) → Num(y,1) → Eq(x,y) → ⊥

    # For now, I'll leave the right HeadMove case as a simple weakening placeholder
    # and move forward with the overall structure. The placeholder won't verify but
    # lets me test the rest.

    # PLACEHOLDER for right case: just produce Eq(hn,ska) with right_and_hm on left
    # Real proof: derive ⊥ from Num(d,0)+Eq(d,d1)+Num(d1,1), then weaken.
    got_eq_hn_right = Proof(Sequent([right_and_hm], [eq_hn_ska]),
        'weakening_right', [Proof(Sequent([right_and_hm], []), 'axiom',
            principal=right_and_hm)], principal=eq_hn_ska)
    # HACK: This will fail verification. Need proper ⊥ proof.
    # TODO: prove right case contradiction

    # For now, skip right case. Use only left case and see how far we get.
    # Actually, I can't skip or_elim — HeadMove IS an Or on the left.
    # Let me just use the left case directly by proving Or is the left disjunct.
    # No — HeadMove is ASSUMED, we don't know which disjunct.

    # Let me just leave the whole thing as NotImplementedError for now
    # and explain the status.
"""




def phase1_step_tmstep():
    """Sub-goal 2c+2d: construct next config and prove TMStep.
    |- ∀delta,q0,ka,ska,tape_in,ca,one,d1.
         Function(delta) → TMTransition(delta,q0,one,one,d1,q0) →
         TMConfig(ca,q0,ka,tape_in) → Function(tape_in) →
         Apply(tape_in,ka,one) → Num(d1,1) → Successor(ska,ka) →
         ∃ca_new. And(TMConfig(ca_new, q0, ska, tape_in), TMStep(delta, ca, ca_new))

    Composes:
    1. ordpair_exists + config_intro → construct ca_new, prove TMConfig
    2. TMStep body (9 foralls, 5 premises → Config conclusion):
       a. config_decompose → Eq(q,q0), Eq(h,ka), Eq(tape,tape_in)
       b. apply_func_transfer + func_unique → Eq(sym,one)
       c. transition_unique → Eq(w,one), Eq(d,d1), Eq(qn,q0)
       d. headmove_right_elim → Eq(hn,ska)
       e. tape_update_eq → Eq(tapen,tape_in)
       f. config_eq_transfer → TMConfig(ca_new, qn, hn, tapen)
    3. And + eir to wrap result.
    """
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        eq_symmetric, eq_transitive)
    from theorems.sets import ordpair_exists
    from theorems.omega import func_unique_thm
    from theorems.tm import (config_intro, config_decompose, apply_func_transfer,
        transition_unique, headmove_right_elim, config_eq_transfer, tape_update_eq)
    from vocab.functions import Function as FuncDef
    from core.proof import Proof, Sequent, same
    from core.derived import Exists
    import core.zfc as zfc

    delta = Var(postfix='delta')
    q0 = Var(postfix='q0')
    ka = Var(postfix='ka')
    ska = Var(postfix='ska')
    tape_in = Var(postfix='tin')
    ca = Var(postfix='ca')
    one = Var(postfix='one')
    d1 = Var(postfix='d1')

    cfg_ca = TMConfig(ca, q0, ka, tape_in)
    app_tape_ka = Apply(tape_in, ka, one)
    trans_known = TMTransition(delta, q0, one, one, d1, q0)
    num_d1 = Num(d1, 1)
    succ_ska = Successor(ska, ka)
    func_delta = FuncDef(delta)
    func_tape = FuncDef(tape_in)

    # === Part 1: Construct ca_new and TMConfig(ca_new, q0, ska, tape_in) ===
    oe = ordpair_exists()
    ca_new = Var(postfix='cn')
    inner_new = Var(postfix='in2')
    op_inner_new = OrdPair(inner_new, ska, tape_in)
    op_ca_new = OrdPair(ca_new, q0, inner_new)
    got_ex_inner = apply_thm(oe, [ska, tape_in], concl=Exists(inner_new, op_inner_new))
    got_ex_ca = apply_thm(oe, [q0, inner_new], concl=Exists(ca_new, op_ca_new))

    ci = config_intro()
    cfg_new = TMConfig(ca_new, q0, ska, tape_in)
    got_cfg_new = apply_thm(ci, [ca_new, q0, ska, tape_in, inner_new])
    got_cfg_new = mp(got_cfg_new, ax(op_inner_new), op_inner_new,
        Implies(op_ca_new, cfg_new))
    got_cfg_new = mp(got_cfg_new, ax(op_ca_new), op_ca_new, cfg_new)
    # [Pairing, OrdPair(inner_new,...), OrdPair(ca_new,...)] |- TMConfig(ca_new,q0,ska,tape_in)

    # === Part 2: Prove TMStep(delta, ca, ca_new) ===
    # TMStep = ∀q,h,tape,sym,w,d,qn,hn,tapen.
    #   Config(ca,q,h,tape) → Apply(tape,h,sym) → Trans(delta,q,sym,w,d,qn) →
    #   TapeUpdate(tapen,tape,h,w) → HeadMove(h,hn,d) → Config(ca_new,qn,hn,tapen)

    q = Var(postfix='sq')
    h = Var(postfix='sh')
    tape = Var(postfix='st')
    sym = Var(postfix='ss')
    w = Var(postfix='sw')
    d = Var(postfix='sd')
    qn = Var(postfix='sqn')
    hn = Var(postfix='shn')
    tapen = Var(postfix='stn')

    p_cfg = TMConfig(ca, q, h, tape)
    p_read = Apply(tape, h, sym)
    p_trans = TMTransition(delta, q, sym, w, d, qn)
    p_upd = TapeUpdate(tapen, tape, h, w)
    p_move = HeadMove(h, hn, d)
    p_goal = TMConfig(ca_new, qn, hn, tapen)

    # Step 2a: config_decompose → Eq(q,q0), Eq(h,ka), Eq(tape,tape_in)
    cd = config_decompose()
    eq_q = Eq(q, q0)
    eq_h = Eq(h, ka)
    eq_t = Eq(tape, tape_in)
    and_3eq = And(eq_q, And(eq_h, eq_t))
    got_3eq = apply_thm(cd, [ca, q, h, tape, q0, ka, tape_in])
    got_3eq = mp(got_3eq, ax(p_cfg), p_cfg, Implies(cfg_ca, and_3eq))
    got_3eq = mp(got_3eq, ax(cfg_ca), cfg_ca, and_3eq)
    # [Pairing, p_cfg, cfg_ca] |- And(Eq(q,q0), And(Eq(h,ka), Eq(tape,tape_in)))

    got_eq_q = apply_thm(and_elim_left(eq_q, And(eq_h, eq_t), []), [],
        and_3eq, eq_q, got_3eq)
    got_eq_ht = apply_thm(and_elim_right(eq_q, And(eq_h, eq_t), []), [],
        and_3eq, And(eq_h, eq_t), got_3eq)
    got_eq_h = apply_thm(and_elim_left(eq_h, eq_t, []), [],
        And(eq_h, eq_t), eq_h, got_eq_ht)
    got_eq_t = apply_thm(and_elim_right(eq_h, eq_t, []), [],
        And(eq_h, eq_t), eq_t, got_eq_ht)

    # Step 2b: apply_func_transfer + func_unique → Eq(sym,one)
    # Transfer Apply(tape,h,sym) to Apply(tape_in,h,sym) via Eq(tape,tape_in)
    aft = apply_func_transfer()
    app_tin_h_sym = Apply(tape_in, h, sym)
    got_app_tin = apply_thm(aft, [tape, tape_in, h, sym])
    got_app_tin = mp(got_app_tin, got_eq_t, eq_t, Implies(p_read, app_tin_h_sym))
    got_app_tin = mp(got_app_tin, ax(p_read), p_read, app_tin_h_sym)
    # [..., p_read] |- Apply(tape_in, h, sym)

    # Transfer Apply(tape_in,h,sym) to Apply(tape_in,ka,sym) via eq_apply_transfer + Eq(h,ka)
    from theorems.recursion import eq_apply_transfer
    eat = eq_apply_transfer()
    app_tin_ka_sym = Apply(tape_in, ka, sym)
    got_app_ka_sym = mp(apply_thm(eat, [tape_in, h, ka, sym], eq_h,
        Implies(app_tin_h_sym, app_tin_ka_sym), got_eq_h),
        got_app_tin, app_tin_h_sym, app_tin_ka_sym)

    # func_unique: Function(tape_in) → Apply(tape_in,ka,sym) → Apply(tape_in,ka,one) → Eq(sym,one)
    fu = func_unique_thm()
    eq_sym = Eq(sym, one)
    got_fu = apply_thm(fu, [tape_in, ka, sym, one])
    got_fu = mp(got_fu, ax(func_tape), func_tape, got_fu.sequent.right[0].right)
    got_fu = mp(got_fu, got_app_ka_sym, app_tin_ka_sym, got_fu.sequent.right[0].right)
    got_eq_sym = mp(got_fu, ax(app_tape_ka), app_tape_ka, eq_sym)

    # Step 2c: transition_unique → Eq(w,one), Eq(d,d1), Eq(qn,q0)
    # Need TMTransition(delta,q,sym,w,d,qn) and TMTransition(delta,q,sym,one,d1,q0)
    # But trans_known is TMTransition(delta,q0,one,one,d1,q0), not (delta,q,sym,...).
    # Use Eq(q,q0) + Eq(sym,one) to see they have same effective input.
    # transition_unique expects TWO transitions with SAME (delta,q,sym).
    # We have p_trans = TMTransition(delta,q,sym,w,d,qn) and
    # trans_known = TMTransition(delta,q0,one,one,d1,q0).
    # These have different q,sym args. We need to build TMTransition(delta,q,sym,one,d1,q0)
    # from trans_known + Eq(q,q0) + Eq(sym,one).
    # Alternative: instantiate transition_unique with the KNOWN transition's args,
    # and transfer p_trans's args.

    # Actually simpler: transition_unique(delta, q, sym, w, d, qn, one, d1, q0):
    # Function(delta) → TMTransition(delta,q,sym,w,d,qn) → TMTransition(delta,q,sym,one,d1,q0) → Eq's
    # We need TMTransition(delta,q,sym,one,d1,q0). This is NOT the same as trans_known
    # (which has q0,one instead of q,sym). But the engine checks alpha-equiv after expansion.
    # TMTransition expands to Apply(delta, (q,sym), (w,(d,qn))). So TMTransition(delta,q,sym,one,d1,q0)
    # gives Apply(delta, (q,sym), (one,(d1,q0))). And trans_known = TMTransition(delta,q0,one,one,d1,q0)
    # gives Apply(delta, (q0,one), (one,(d1,q0))).
    # These are different (different inp pair). Can't directly use transition_unique.

    # Better approach: use Eq(q,q0) + Eq(sym,one) to transfer trans_known to same args.
    # TMTransition is a definition. We need to show TMTransition(delta,q,sym,one,d1,q0)
    # from TMTransition(delta,q0,one,one,d1,q0) + Eq(q,q0) + Eq(sym,one).
    # This requires "TMTransition is invariant under Eq on input args."
    # Since TMTransition builds OrdPair(inp,state,sym) internally, and we're just
    # changing the state/sym args, the Apply(delta,inp,out) with a different inp pair...
    # this is NOT a simple transfer.

    # Simplest approach: don't use transition_unique. Instead, inline the func_unique
    # approach on delta. We have p_trans and trans_known, both give Apply(delta,...).
    # Instantiate both with the SAME inp pair (built from q,sym), use func_unique.

    # Build common inp pair from (q, sym):
    inp = Var(postfix='inp')
    op_inp_qs = OrdPair(inp, q, sym)
    got_ex_inp = apply_thm(oe, [q, sym], concl=Exists(inp, op_inp_qs))

    # From p_trans(delta,q,sym,w,d,qn) with inp: Apply(delta,inp,out1) for some out1
    dp1 = Var(postfix='dp1')
    out1 = Var(postfix='out1')
    op_dp1 = OrdPair(dp1, d, qn)
    op_out1 = OrdPair(out1, w, dp1)
    got_ex_dp1 = apply_thm(oe, [d, qn], concl=Exists(dp1, op_dp1))
    got_ex_out1 = apply_thm(oe, [w, dp1], concl=Exists(out1, op_out1))

    app_d_out1 = Apply(delta, inp, out1)
    got_t1 = apply_thm(ax(p_trans), [inp], op_inp_qs,
        Forall(dp1, Implies(op_dp1, Forall(out1, Implies(op_out1, app_d_out1)))), ax(op_inp_qs))
    got_t1 = apply_thm(got_t1, [dp1], op_dp1,
        Forall(out1, Implies(op_out1, app_d_out1)), ax(op_dp1))
    got_t1 = apply_thm(got_t1, [out1], op_out1, app_d_out1, ax(op_out1))

    # From trans_known(delta,q0,one,one,d1,q0) with inp:
    # trans_known expects OrdPair(inp,q0,one). Transfer from OrdPair(inp,q,sym):
    from theorems.sets import ordpair_eq_transfer
    oet = ordpair_eq_transfer()
    op_inp_q0one = OrdPair(inp, q0, one)
    got_inp_transfer = apply_thm(oet, [q, sym, q0, one, inp])
    got_inp_transfer = mp(got_inp_transfer, got_eq_q, eq_q, got_inp_transfer.sequent.right[0].right)
    got_inp_transfer = mp(got_inp_transfer, got_eq_sym, eq_sym, got_inp_transfer.sequent.right[0].right)
    got_inp_transfer = mp(got_inp_transfer, ax(op_inp_qs), op_inp_qs, op_inp_q0one)

    dp2 = Var(postfix='dp2')
    out2 = Var(postfix='out2')
    op_dp2 = OrdPair(dp2, d1, q0)
    op_out2 = OrdPair(out2, one, dp2)
    got_ex_dp2 = apply_thm(oe, [d1, q0], concl=Exists(dp2, op_dp2))
    got_ex_out2 = apply_thm(oe, [one, dp2], concl=Exists(out2, op_out2))

    app_d_out2 = Apply(delta, inp, out2)
    # TMTransition(delta,q0,one,one,d1,q0) instantiated with inp:
    # OrdPair(inp,q0,one) → ∀dp2. OrdPair(dp2,d1,q0) → ∀out2. OrdPair(out2,one,dp2) → Apply(delta,inp,out2)
    got_t2 = apply_thm(ax(trans_known), [inp], op_inp_q0one,
        Forall(dp2, Implies(op_dp2, Forall(out2, Implies(op_out2, app_d_out2)))),
        ax(op_inp_q0one))
    got_t2 = apply_thm(got_t2, [dp2], op_dp2,
        Forall(out2, Implies(op_out2, app_d_out2)), ax(op_dp2))
    got_t2 = apply_thm(got_t2, [out2], op_out2, app_d_out2, ax(op_out2))
    # [trans_known, OrdPair(inp,q0,one), op_dp2, op_out2] |- Apply(delta,inp,out2)
    got_t2 = cut(got_t2, op_inp_q0one, got_inp_transfer)

    # func_unique on delta: Eq(out1, out2)
    eq_out = Eq(out1, out2)
    got_eq_out = apply_thm(fu, [delta, inp, out1, out2])
    got_eq_out = mp(got_eq_out, ax(func_delta), func_delta, got_eq_out.sequent.right[0].right)
    got_eq_out = mp(got_eq_out, got_t1, app_d_out1, got_eq_out.sequent.right[0].right)
    got_eq_out = mp(got_eq_out, got_t2, app_d_out2, eq_out)

    # tuple_injection: Eq(out1,out2) + OrdPair(out1,w,dp1) + OrdPair(out2,one,dp2) → Eq(w,one), Eq(dp1,dp2)
    from theorems.sets import ordpair_set_transfer, tuple_injection
    ti = tuple_injection()
    ost = ordpair_set_transfer()

    op_out1_from2 = OrdPair(out1, one, dp2)
    got_out1_from2 = mp(apply_thm(ost, [out1, out2, one, dp2], eq_out,
        Implies(op_out2, op_out1_from2), got_eq_out),
        ax(op_out2), op_out2, op_out1_from2)
    eq_w_one = Eq(w, one)
    eq_dp12 = Eq(dp1, dp2)
    got_ti_out = apply_thm(ti, [w, dp1, one, dp2, out1])
    got_ti_out = mp(got_ti_out, ax(op_out1), op_out1, Implies(op_out1_from2, And(eq_w_one, eq_dp12)))
    got_ti_out = mp(got_ti_out, got_out1_from2, op_out1_from2, And(eq_w_one, eq_dp12))
    got_eq_w = apply_thm(and_elim_left(eq_w_one, eq_dp12, []), [], And(eq_w_one, eq_dp12), eq_w_one, got_ti_out)
    got_eq_dp = apply_thm(and_elim_right(eq_w_one, eq_dp12, []), [], And(eq_w_one, eq_dp12), eq_dp12, got_ti_out)

    # tuple_injection on dp: Eq(dp1,dp2) + OrdPair(dp1,d,qn) + OrdPair(dp2,d1,q0) → Eq(d,d1), Eq(qn,q0)
    op_dp1_from2 = OrdPair(dp1, d1, q0)
    got_dp1_from2 = mp(apply_thm(ost, [dp1, dp2, d1, q0], eq_dp12,
        Implies(op_dp2, op_dp1_from2), got_eq_dp),
        ax(op_dp2), op_dp2, op_dp1_from2)
    eq_d = Eq(d, d1)
    eq_qn = Eq(qn, q0)
    got_ti_dp = apply_thm(ti, [d, qn, d1, q0, dp1])
    got_ti_dp = mp(got_ti_dp, ax(op_dp1), op_dp1, Implies(op_dp1_from2, And(eq_d, eq_qn)))
    got_ti_dp = mp(got_ti_dp, got_dp1_from2, op_dp1_from2, And(eq_d, eq_qn))
    got_eq_d = apply_thm(and_elim_left(eq_d, eq_qn, []), [], And(eq_d, eq_qn), eq_d, got_ti_dp)
    got_eq_qn = apply_thm(and_elim_right(eq_d, eq_qn, []), [], And(eq_d, eq_qn), eq_qn, got_ti_dp)

    # Eliminate existential witnesses
    def elim(proof, formula, var, ex_proof):
        if any(same(formula, ff) for ff in proof.sequent.left):
            p = eel(proof, formula, var)
            return cut(p, Exists(var, formula), ex_proof)
        return proof

    for var, formula, ex_p in [
        (out2, op_out2, got_ex_out2), (dp2, op_dp2, got_ex_dp2),
        (out1, op_out1, got_ex_out1), (dp1, op_dp1, got_ex_dp1),
        (inp, op_inp_qs, got_ex_inp)]:
        got_eq_w = elim(got_eq_w, formula, var, ex_p)
        got_eq_d = elim(got_eq_d, formula, var, ex_p)
        got_eq_qn = elim(got_eq_qn, formula, var, ex_p)

    # Step 2d: headmove_right_elim → Eq(hn,ska)
    hre = headmove_right_elim()
    eq_hn = Eq(hn, ska)
    got_eq_hn = apply_thm(hre, [h, hn, d, ka, ska, d1])
    got_eq_hn = mp(got_eq_hn, ax(p_move), p_move, got_eq_hn.sequent.right[0].right)
    got_eq_hn = mp(got_eq_hn, got_eq_h, eq_h, got_eq_hn.sequent.right[0].right)
    got_eq_hn = mp(got_eq_hn, got_eq_d, eq_d, got_eq_hn.sequent.right[0].right)
    got_eq_hn = mp(got_eq_hn, ax(num_d1), num_d1, got_eq_hn.sequent.right[0].right)
    got_eq_hn = mp(got_eq_hn, ax(succ_ska), succ_ska, eq_hn)

    # Step 2e: tape_update_eq → Eq(tapen,tape)
    # Then Eq(tape,tape_in) → Eq(tapen,tape_in) by eq_transitive.
    tue = tape_update_eq()
    eq_tn_t = Eq(tapen, tape)
    # tape_update_eq: Function(tape) → Apply(tape,h,w) → TapeUpdate(tapen,tape,h,w) → Eq(tapen,tape)
    # We have func_tape = Function(tape_in), not Function(tape).
    # Need Function(tape) from Function(tape_in) + Eq(tape,tape_in).
    # Actually tape_update_eq takes its own vars. Instantiate with [tapen, tape, h, w]:
    got_tue = apply_thm(tue, [tapen, tape, h, w])
    # |- Function(tape) → Apply(tape,h,w) → TapeUpdate(tapen,tape,h,w) → Eq(tapen,tape)
    # We have p_upd = TapeUpdate(tapen,tape,h,w) ✓
    # We have p_read = Apply(tape,h,sym), not Apply(tape,h,w). Need Apply(tape,h,w).
    # From Eq(sym,one) and Eq(w,one): Eq(sym,w)? No, Eq(w,one) and Eq(sym,one) → Eq(w,sym) by transitivity.
    # Actually we need Apply(tape,h,w). We have Apply(tape,h,sym) and Eq(sym,one) and Eq(w,one).
    # So Eq(w,sym) by: Eq(w,one) + Eq(sym,one) → Eq(w,sym) (both equal one).
    # Then eq_apply_val_transfer: Eq(sym,w) → Apply(tape,h,sym) → Apply(tape,h,w).
    # Wait: Eq(w,one) and Eq(sym,one) means w=one and sym=one, so w=sym.
    # eq_symmetric(sym,one) → Eq(one,sym). eq_transitive(w,one,sym): Eq(w,one)→Eq(one,sym)→Eq(w,sym).
    # Then eq_apply_val_transfer with Eq(sym,w)... hmm, direction.

    # Simpler: transfer Apply(tape,h,sym) to Apply(tape,h,w) via Eq(sym,w).
    # Eq(sym,one) reversed: Eq(one,sym). Eq(w,one): chain Eq(w,one)→Eq(one,sym)→Eq(w,sym).
    es = eq_symmetric()
    et = eq_transitive()
    eq_one_sym = Eq(one, sym)
    got_one_sym = apply_thm(es, [sym, one], eq_sym, eq_one_sym, got_eq_sym)
    eq_w_sym = Eq(w, sym)
    got_w_sym = apply_thm(et, [w, one, sym])
    got_w_sym = mp(got_w_sym, got_eq_w, eq_w_one, Implies(eq_one_sym, eq_w_sym))
    got_w_sym = mp(got_w_sym, got_one_sym, eq_one_sym, eq_w_sym)

    # eq_apply_val_transfer: Eq(y1,y2) → Apply(f,x,y1) → Apply(f,x,y2)
    from theorems.recursion import eq_apply_val_transfer
    eavt = eq_apply_val_transfer()
    # Eq(sym,w) → Apply(tape,h,sym) → Apply(tape,h,w)
    eq_sym_w = Eq(sym, w)
    got_sym_w = apply_thm(es, [w, sym], eq_w_sym, eq_sym_w, got_w_sym)
    app_thw = Apply(tape, h, w)
    got_app_thw = mp(apply_thm(eavt, [tape, h, sym, w], eq_sym_w,
        Implies(p_read, app_thw), got_sym_w),
        ax(p_read), p_read, app_thw)

    # Function(tape): from Function(tape_in) + Eq(tape,tape_in)
    # Actually, tape_update_eq's Function arg is the tape, not tape_in.
    # We need Function(tape). Since Eq(tape,tape_in) and Function is defined via In/Apply,
    # Function(tape) ↔ Function(tape_in). But proving this transfer is complex.
    # Simpler: instantiate tape_update_eq with tape_in directly: [tapen, tape_in, h, w].
    # But p_upd = TapeUpdate(tapen, tape, h, w), not TapeUpdate(tapen, tape_in, h, w).
    # The engine compares formulas structurally, so tape ≠ tape_in.

    # Best approach: first prove Eq(tapen, tape) from tape_update_eq instantiated
    # with the ACTUAL tape/h/w, then chain to Eq(tapen, tape_in).
    # For Function(tape): we can derive it from Function(tape_in) + Eq(tape,tape_in).
    # Function(f) = And(Relation(f), single_valued(f)). Each part transfers via Eq.
    # But this is another ~20 lines.

    # Pragmatic: just assume Function(tape) from the context by using Eq transfer on the whole And.
    # Actually, Function is a definition. Eq(tape, tape_in) means same elements.
    # Function(tape) ↔ Function(tape_in) because Function is defined in terms of In.
    # The transfer: from [Function(tape_in), Eq(tape,tape_in)] derive Function(tape).
    # This requires expanding Function and transferring each In/Apply.

    # SHORTCUT: instantiate tape_update_eq differently. Use:
    # tape_update_eq(tapen, tape_in, ka, one):
    #   Function(tape_in) → Apply(tape_in,ka,one) → TapeUpdate(tapen,tape_in,ka,one) → Eq(tapen,tape_in)
    # But we have TapeUpdate(tapen, tape, h, w), not TapeUpdate(tapen, tape_in, ka, one).
    # The Eq's (tape=tape_in, h=ka, w=one... well w=one via Eq) don't help because
    # TapeUpdate is a structural formula.

    # Most practical: just use the general tape_update_eq with the actual vars,
    # and handle Function(tape) by noting it follows from Eq.
    # Since Function(tape) = And(Relation(tape), ∀x,y1,y2. And(Apply(tape,x,y1),Apply(tape,x,y2))→Eq(y1,y2))
    # and Eq(tape,tape_in) means ∀p. p∈tape ↔ p∈tape_in, every In/Apply fact transfers.
    # This is exactly what apply_func_transfer does for the Apply part.
    # For Relation: Relation(f) = ∀p. p∈f → ∃x,y. OrdPair(p,x,y) ∧ p∈f. Same In-based.

    # Actually I realize the simplest approach: tape_update_eq proves Eq(tapen,tape).
    # Combined with Eq(tape,tape_in) → Eq(tapen,tape_in). That's the final result.
    # For Function(tape): I'll just skip it for now and pass func_tape = Function(tape_in)
    # as a hypothesis to tape_update_eq? No, tape_update_eq expects Function(tape).

    # OK let me just inline the key step: from Eq(tapen,tape) and Eq(tape,tape_in),
    # get Eq(tapen,tape_in). For the Function(tape) prerequisite, I'll build it from
    # Function(tape_in) + Eq(tape,tape_in). This transfer is generic and useful.

    # Actually, rather than building Function(tape) which is very complex,
    # let me take a completely different path for 2e:
    # tape_update_eq with [tapen, tape, h, w] gives:
    #   Function(tape) → Apply(tape,h,w) → TapeUpdate → Eq(tapen,tape)
    # Skip this. Instead, directly show Eq(tapen,tape_in) using:
    #   TapeUpdate(tapen,tape,h,w) + Eq(tape,tape_in) + Eq(h,ka) + Eq(w,one)
    #   + Function(tape_in) + Apply(tape_in,ka,one)
    # This is tape_update_eq instantiated with tape_in/ka/one after the Eq transfers.

    # Since we can't instantiate tape_update_eq with tape_in (different from tape in the formula),
    # we need to transfer TapeUpdate(tapen,tape,h,w) to TapeUpdate(tapen,tape_in,ka,one).
    # But TapeUpdate is a definition — transferring it requires expanding and re-deriving.

    # SIMPLEST: skip tape_update_eq for now. Use Eq(tape,tape_in) + Eq(h,ka) + Eq(w,one)
    # to conclude Eq(tapen,tape) doesn't matter — we just need Eq(tapen,tape_in) for config_eq_transfer.
    # And since config_eq_transfer takes Eq(t1,t2), we actually need Eq(tapen, tape_in).

    # Chain: tape_update_eq gives Eq(tapen, tape) from Function(tape) + Apply(tape,h,w) + TapeUpdate.
    # Then Eq(tape, tape_in) from 2a. Then Eq(tapen, tape_in) by eq_transitive.
    # The Function(tape) problem remains.

    # Final approach: I'll prove a one-off "Function transfers across Eq":
    # Eq(f,g) + Function(f) → Function(g). This is true because Function is In-based.
    # But I don't have this theorem. Let me use the reverse: Eq(tape_in,tape) + Function(tape_in) → Function(tape).
    # Since Eq is extensional (same elements), And(Relation(tape),sv(tape)) iff And(Relation(tape_in),sv(tape_in)).
    # This is a deep transfer. Not worth building inline.

    # PRAGMATIC DECISION: For now, add Function(tape) as a premise of TMStep body.
    # It's immediately available from Function(tape_in) + Eq(tape,tape_in) in principle,
    # but proving the transfer would take ~30 lines. TMStep's universal quantifiers
    # already encompass tape, so having Function(tape) as a premise is reasonable.

    # NO WAIT: I can be smarter. tape_update_eq needs Function + Apply + TapeUpdate.
    # But I have Apply(tape,h,w) already from got_app_thw. And TapeUpdate is p_upd.
    # The only missing piece is Function(tape).
    # Since tape is universally quantified in TMStep, I CAN'T have Function(tape) from outside.
    # It MUST come from Function(tape_in) + Eq(tape,tape_in).

    # Let me just handle this via the Eq expansion. Eq(tape,tape_in) means ∀p. p∈tape ↔ p∈tape_in.
    # Function(tape_in) = And(Rel(tape_in), sv(tape_in)).
    # Rel(tape_in) = ∀p. p∈tape_in → ∃x,y. OrdPair(p,x,y). With Eq: same for tape.
    # sv(tape_in) = ∀x,y1,y2. And(Apply(tape_in,x,y1),Apply(tape_in,x,y2)) → Eq(y1,y2).
    # Apply(tape_in,x,y) = ∃p. OrdPair(p,x,y) ∧ p∈tape_in. With Eq: same for tape.
    # So Function(tape) follows. But formalizing this is a 30-line theorem.

    # For NOW: I'll use tape_update_eq's conclusion directly by proving
    # Eq(tapen,tape_in) a different way. Instead of tape_update_eq,
    # use: Eq(tape,tape_in) and apply_func_transfer to move TapeUpdate's characterization,
    # then derive Eq(tapen,tape_in) from Extensionality.
    # But this is essentially re-proving tape_update_eq inline.

    # ACTUAL SIMPLEST: use eq_transitive. I have Eq(tapen,tape) (from tape_update_eq
    # if I can supply Function(tape)) and Eq(tape,tape_in).
    # For Function(tape), expand func_tape=Function(tape_in) and transfer.
    # Let me just write a tiny inline transfer for Function.

    # Function(f) = And(Relation(f), single_valued(f)).
    # Actually, for tape_update_eq, only the single_valued part is used (func_unique inside).
    # And single_valued uses Apply which uses In. With Eq(tape,tape_in), every In(p,tape)↔In(p,tape_in).
    # So Apply(tape,x,y)↔Apply(tape_in,x,y). And single_valued transfers.
    # But Relation also transfers.
    # The whole Function transfers via Eq.

    # I think the cleanest is to skip tape_update_eq entirely and instead
    # prove Eq(tapen, tape_in) directly from the Eq chain:
    # tape ≡ tape_in (Eq), h ≡ ka, w ≡ one.
    # TapeUpdate(tapen, tape, h, w) characterizes tapen based on tape/h/w.
    # After substituting equivalents: tapen is characterized by tape_in/ka/one.
    # tape_in already has one at ka. So tapen ≡ tape_in.
    # But this IS tape_update_eq, just with transferred args.

    # OK I'll just build Function(tape) from Function(tape_in) + Eq(tape,tape_in)
    # by using apply_func_transfer on the definition. Since I already proved
    # apply_func_transfer, I can transfer each Apply inside Function's definition.

    # Actually, the truly simplest: eq_transitive gives Eq(A,C) from Eq(A,B)+Eq(B,C).
    # I need Eq(tapen, tape_in).
    # Path 1: Eq(tapen, tape) + Eq(tape, tape_in) → Eq(tapen, tape_in). Need Eq(tapen,tape).
    # Path 2: Just prove Eq(tapen, tape_in) directly from TapeUpdate + Eq transfers.

    # For Path 1, tape_update_eq(tapen, tape, h, w) needs Function(tape).
    # Let me just admit we need a func_eq_transfer helper and leave a TODO.
    # OR: skip the tape Eq entirely and use config_eq_transfer with Eq(tapen, tape_in)
    # obtained by chaining Eq(tapen, tape) + Eq(tape, tape_in) — same problem.

    # DECISION: For the TMStep proof, the 9 vars include tapen. The conclusion
    # needs TMConfig(ca_new, qn, hn, tapen). With config_eq_transfer, I need
    # Eq(tape_in, tapen). But I can't easily get this without tape_update_eq.
    # Let me just use tape_update_eq with Function(tape) obtained from cut with
    # a "func_transfer" proof. The func_transfer is: Eq(tape,tape_in) → Function(tape_in) → Function(tape).
    # I'll prove it inline using the definition expansion.

    # INLINE func_transfer: Eq(tape,tape_in) + Function(tape_in) → Function(tape)
    # Function = And(Relation, single_valued). Both use In-based patterns.
    # With Eq(tape,tape_in) = ∀p. p∈tape ↔ p∈tape_in, transfer each In.

    # Actually, I just realized: Eq(tape, tape_in) IS the bidirectional membership.
    # Function(tape) after expansion uses In(p, tape) etc.
    # The engine checks formulas via expansion + alpha-equivalence.
    # Function(tape).expand() and Function(tape_in).expand() differ by tape vs tape_in.
    # They're NOT alpha-equivalent. So we need real proof work.

    # Fine. Let me just use ax(func_tape) and wl it into the TMStep body context.
    # But Function(tape_in) is NOT Function(tape). The engine won't accept it as a substitute.

    # I'll write func_eq_transfer as a quick helper and use it.
    # For now, leave as TODO and test the rest.

    # Step 2e: Eq(tapen, tape_in) via tape_update_eq + func_eq_transfer + eq_transitive
    # func_eq_transfer: Eq(tape, tape_in) + Function(tape_in) → Function(tape)
    from theorems.tm import func_eq_transfer
    fet = func_eq_transfer()
    es_t = eq_symmetric()
    eq_tin_t = Eq(tape_in, tape)
    got_eq_tin_t = apply_thm(es_t, [tape, tape_in], eq_t, eq_tin_t, got_eq_t)
    func_tape_v = FuncDef(tape)
    got_func_tape = apply_thm(fet, [tape_in, tape])
    got_func_tape = mp(got_func_tape, got_eq_tin_t, eq_tin_t, Implies(func_tape, func_tape_v))
    got_func_tape = mp(got_func_tape, ax(func_tape), func_tape, func_tape_v)
    # [...] |- Function(tape)

    # tape_update_eq: Function(tape) → Apply(tape,h,w) → TapeUpdate(tapen,tape,h,w) → Eq(tapen,tape)
    eq_tn_t = Eq(tapen, tape)
    got_eq_tn_t = apply_thm(tue, [tapen, tape, h, w])
    got_eq_tn_t = mp(got_eq_tn_t, got_func_tape, func_tape_v, got_eq_tn_t.sequent.right[0].right)
    got_eq_tn_t = mp(got_eq_tn_t, got_app_thw, app_thw, got_eq_tn_t.sequent.right[0].right)
    got_eq_tn_t = mp(got_eq_tn_t, ax(p_upd), p_upd, eq_tn_t)
    # [..., p_upd] |- Eq(tapen, tape)

    # eq_transitive: Eq(tapen,tape) + Eq(tape,tape_in) → Eq(tapen,tape_in)
    eq_tn_tin = Eq(tapen, tape_in)
    got_eq_tn_tin = apply_thm(et, [tapen, tape, tape_in])
    got_eq_tn_tin = mp(got_eq_tn_tin, got_eq_tn_t, eq_tn_t, Implies(eq_t, eq_tn_tin))
    got_eq_tn_tin = mp(got_eq_tn_tin, got_eq_t, eq_t, eq_tn_tin)
    # [...] |- Eq(tapen, tape_in)

    # Step 2f: config_eq_transfer → TMConfig(ca_new, qn, hn, tapen)
    cet = config_eq_transfer()
    got_cfg_goal = apply_thm(cet, [ca_new, q0, ska, tape_in, qn, hn, tapen])
    got_cfg_goal = mp(got_cfg_goal, got_cfg_new, cfg_new, got_cfg_goal.sequent.right[0].right)
    # Need Eq(q0,qn): from Eq(qn,q0), reverse
    eq_q0_qn = Eq(q0, qn)
    got_eq_q0_qn = apply_thm(es, [qn, q0], eq_qn, eq_q0_qn, got_eq_qn)
    got_cfg_goal = mp(got_cfg_goal, got_eq_q0_qn, eq_q0_qn, got_cfg_goal.sequent.right[0].right)
    # Need Eq(ska,hn): from Eq(hn,ska), reverse
    eq_ska_hn = Eq(ska, hn)
    got_eq_ska_hn = apply_thm(es, [hn, ska], eq_hn, eq_ska_hn, got_eq_hn)
    got_cfg_goal = mp(got_cfg_goal, got_eq_ska_hn, eq_ska_hn, got_cfg_goal.sequent.right[0].right)
    # Need Eq(tape_in,tapen): from Eq(tapen,tape_in), reverse
    eq_tin_tn = Eq(tape_in, tapen)
    got_eq_tin_tn = apply_thm(es, [tapen, tape_in], eq_tn_tin, eq_tin_tn, got_eq_tn_tin)
    got_cfg_goal = mp(got_cfg_goal, got_eq_tin_tn, eq_tin_tn, p_goal)
    # [...] |- TMConfig(ca_new, qn, hn, tapen)

    # === Discharge 5 TMStep premises + close 9 foralls ===
    proof_body = got_cfg_goal
    for premise in [p_move, p_upd, p_trans, p_read, p_cfg]:
        imp = Implies(premise, proof_body.sequent.right[0])
        proof_body = Proof(Sequent(
            [f for f in proof_body.sequent.left if not same(f, premise)] + [premise],
            [proof_body.sequent.right[0]]),
            'weakening_left', [proof_body], principal=premise) if not any(same(premise, f) for f in proof_body.sequent.left) else proof_body
        imp = Implies(premise, proof_body.sequent.right[0])
        left = [f for f in proof_body.sequent.left if not same(f, premise)]
        proof_body = Proof(Sequent(left, [imp]), 'implies_right', [proof_body], principal=imp)

    # Cut Eq(tapen,tape_in) from left with actual proof
    if any(same(eq_tn_tin, f) for f in proof_body.sequent.left):
        proof_body = cut(proof_body, eq_tn_tin, got_eq_tn_tin)

    for v in [tapen, hn, qn, d, w, sym, tape, h, q]:
        body = proof_body.sequent.right[0]
        fa = Forall(v, body)
        proof_body = Proof(Sequent(proof_body.sequent.left, [fa]),
            'forall_right', [proof_body], principal=fa, term=v)
    # [...external ctx...] |- TMStep(delta, ca, ca_new)

    # === Part 3: And(TMConfig, TMStep) + eir ca_new ===
    tmstep = TMStep(delta, ca, ca_new)
    ai = and_intro(cfg_new, tmstep, [])
    got_and = mp(apply_thm(ai, [], cfg_new, Implies(tmstep, And(cfg_new, tmstep)), got_cfg_new),
        proof_body, tmstep, And(cfg_new, tmstep))

    # eir ca_new: wrap right in ∃ca_new
    got_ex = eir(got_and, And(cfg_new, tmstep), ca_new, ca_new)
    # eel ca_new from op_ca_new on left, then cut with got_ex_ca
    got_ex = eel(got_ex, op_ca_new, ca_new)
    got_ex = cut(got_ex, Exists(ca_new, op_ca_new), got_ex_ca)
    # eel inner_new from op_inner_new on left, then cut with got_ex_inner
    got_ex = eel(got_ex, op_inner_new, inner_new)
    got_ex = cut(got_ex, Exists(inner_new, op_inner_new), got_ex_inner)

    # Discharge hypotheses, close ∀
    proof = got_ex
    hyps = [Successor(ska, ka), Num(d1, 1), Apply(tape_in, ka, one),
            FuncDef(tape_in), TMConfig(ca, q0, ka, tape_in),
            TMTransition(delta, q0, one, one, d1, q0), FuncDef(delta)]
    for hyp in hyps:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [d1, one, ca, tape_in, ska, ka, q0, delta]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'phase1_step_tmstep'
    return proof


# Dead code removed — the following were inline attempts now replaced by sub-helper stubs.
# Keeping this marker for reference.


def phase1_step_extend_trace():
    """Sub-goal 2e+2f: extend trace and build P1(S(ka)) body.

    Hypotheses (on left):
      Function(tra) — trace is a function
      ∀z'. Empty(z') → Apply(tra, z', c0) — base condition from P1(ka)
      Apply(tra, ka, ca) — trace at ka from P1(ka)
      step_valid(tra, ka) — old step validity from P1(ka)
      TMStep(delta, ca, ca_new) — the step [from tmstep]
      Successor(ska, ka) — ska = S(ka)
      Omega(w), In(ka, w) — omega context for anti-reflexivity
      Pairing, Union_ax

    Returns proof of: ∃tra_new.
      And(Function(tra_new),
      And(∀z'. Empty(z') → Apply(tra_new, z', c0),
      And(Apply(tra_new, ska, ca_new),
          step_valid(tra_new, ska))))
    """
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        eq_symmetric, or_elim, iff_mp, iff_mp_rev)
    from theorems.sets import (ordpair_exists, singleton_exists, union_exists,
        ordpair_val_transfer, omega_transitive_set, omega_no_self_membership)
    from theorems.recursion import (apply_singleton, apply_union_intro_left,
        apply_union_intro_right, apply_union_elim, singleton_apply_eq,
        extend_function, eq_apply_transfer, eq_apply_val_transfer)
    from theorems.omega import func_unique_thm
    from vocab.sets import Singleton as Sing, Union as UnionDef, TransitiveSet
    from vocab.functions import Function as FuncDef
    from vocab.omega import Omega
    from core.proof import Proof, Sequent, same
    from core.derived import Exists, Or
    import core.zfc as zfc

    tra = Var(postfix='tra')
    tra_new = Var(postfix='trn')
    ska = Var(postfix='ska')
    ca_new = Var(postfix='cn')
    z = Var(postfix='z')
    c0 = Var(postfix='c0')
    ka = Var(postfix='ka')
    delta = Var(postfix='delta')
    ca = Var(postfix='ca')
    ja = Var(postfix='ja')
    sja = Var(postfix='sja')
    cja = Var(postfix='cja')
    cja1 = Var(postfix='cja1')
    w = Var(postfix='w')

    succ_ska = Successor(ska, ka)
    tmstep_ca = TMStep(delta, ca, ca_new)
    func_tra = FuncDef(tra)
    omega_w = Omega(w)
    in_ka_w = In(ka, w)
    app_tra_ka_ca = Apply(tra, ka, ca)

    step_valid_old = Forall(ja, Implies(In(ja, ka),
        Forall(sja, Implies(Successor(sja, ja),
            Forall(cja, Implies(Apply(tra, ja, cja),
                Exists(cja1, And(Apply(tra, sja, cja1), TMStep(delta, cja, cja1)))))))))

    oe = ordpair_exists()
    base_old = Forall(z, Implies(Empty(z), Apply(tra, z, c0)))

    # === 1. Construct tra_new = tra ∪ {(ska, ca_new)} ===
    pair_ska = Var(postfix='pska')
    op_pair_ska = OrdPair(pair_ska, ska, ca_new)
    got_ex_pair = apply_thm(oe, [ska, ca_new], concl=Exists(pair_ska, op_pair_ska))

    sing = Var(postfix='sing')
    sing_def = Sing(sing, pair_ska)
    se = singleton_exists()
    got_ex_sing = apply_thm(se, [pair_ska], concl=Exists(sing, sing_def))

    union_def = UnionDef(tra_new, tra, sing)
    ue = union_exists()
    got_ex_union = apply_thm(ue, [tra, sing], concl=Exists(tra_new, union_def))

    aul = apply_union_intro_left()
    aur = apply_union_intro_right()

    # === Helper: derive ⊥ from In(ska,ka) via omega context ===
    # In(ska,ka) + TransitiveSet(ka) → ska⊆ka → ka∈ska → ka∈ka.
    # omega_no_self_membership: ¬In(ka,ka). Contradiction.
    def bot_from_in_ska_ka(got_in_ska_ka):
        """Given proof of [...] |- In(ska,ka), derive [..., Omega(w), In(ka,w)] |- ⊥."""
        ots = omega_transitive_set()
        got_trans_ka = apply_thm(ots, [w, ka])
        got_trans_ka = mp(got_trans_ka, ax(omega_w), omega_w,
            Implies(in_ka_w, TransitiveSet(ka)))
        got_trans_ka = mp(got_trans_ka, ax(in_ka_w), in_ka_w, TransitiveSet(ka))
        # [...] |- TransitiveSet(ka)

        # TransitiveSet(ka): ∀x.In(x,ka)→∀y.In(y,x)→In(y,ka).
        # Instantiate x=ska: In(ska,ka)→∀y.In(y,ska)→In(y,ka)
        yv = Var(postfix='yv')
        got_ska_sub = apply_thm(got_trans_ka, [ska], In(ska, ka),
            Forall(yv, Implies(In(yv, ska), In(yv, ka))), got_in_ska_ka)
        # Instantiate y=ka: In(ka,ska)→In(ka,ka)
        got_ka_in_ka = apply_thm(got_ska_sub, [ka])
        # Need In(ka,ska) from Successor(ska,ka): ka∈ska ↔ Or(In(ka,ka), Eq(ka,ka))
        from theorems.logic import eq_reflexive, or_intro_right
        er = eq_reflexive()
        eq_kaka = Eq(ka, ka)
        got_eq_kk = apply_thm(er, [ka], concl=eq_kaka)
        in_ka_ska = In(ka, ska)
        iff_ka_ska = Iff(in_ka_ska, Or(In(ka, ka), eq_kaka))
        got_or_kk = apply_thm(or_intro_right(In(ka,ka), eq_kaka, []), [],
            eq_kaka, Or(In(ka,ka), eq_kaka), got_eq_kk)
        got_in_ka_ska = mp(apply_thm(iff_mp_rev(in_ka_ska, Or(In(ka,ka), eq_kaka), []),
            [], iff_ka_ska, Implies(Or(In(ka,ka), eq_kaka), in_ka_ska),
            fl(succ_ska, iff_ka_ska, ka)),
            got_or_kk, Or(In(ka,ka), eq_kaka), in_ka_ska)

        while type(got_ka_in_ka.sequent.right[0]).__name__ == 'Implies':
            cur = got_ka_in_ka.sequent.right[0]
            got_ka_in_ka = mp(got_ka_in_ka, got_in_ka_ska, in_ka_ska, cur.right) if same(cur.left, in_ka_ska) else mp(got_ka_in_ka, ax(cur.left), cur.left, cur.right)
        # [...] |- In(ka,ka)

        # omega_no_self_membership: ¬In(ka,ka)
        onsm = omega_no_self_membership()
        not_ka_ka = Not(In(ka, ka))
        got_not_kk = apply_thm(onsm, [w, ka])
        got_not_kk = mp(got_not_kk, ax(omega_w), omega_w, Implies(in_ka_w, not_ka_ka))
        got_not_kk = mp(got_not_kk, ax(in_ka_w), in_ka_w, not_ka_ka)

        # Contradiction
        got_ka_w = weaken_to(got_ka_in_ka, list(got_not_kk.sequent.left))
        got_not_w = weaken_to(got_not_kk, list(got_ka_w.sequent.left))
        ctx = list(got_ka_w.sequent.left)
        got_bot_nl = Proof(Sequent(ctx + [not_ka_ka], []),
            'not_left', [got_ka_w], principal=not_ka_ka)
        return Proof(Sequent(ctx, []), 'cut',
            [got_not_w, got_bot_nl], principal=not_ka_ka)

    # === Helper: singleton_apply_eq gives Eq's, then In(ska,ka) → ⊥ → anything ===
    def bot_from_sing_apply(got_app_sing_ja_cja, target):
        """From Apply(sing,ja,cja) + In(ja,ka) + omega context, derive target via ⊥."""
        sae = singleton_apply_eq()
        eq_ja_ska = Eq(ska, ja)  # sae gives Eq(x,e)=Eq(ska,ja), Eq(y,a)=Eq(cja,ca_new)
        and_eqs = And(eq_ja_ska, Eq(ca_new, cja))
        got_eqs = apply_thm(sae, [ska, ca_new, pair_ska, sing, ja, cja])
        got_eqs = mp(got_eqs, ax(op_pair_ska), op_pair_ska, got_eqs.sequent.right[0].right)
        got_eqs = mp(got_eqs, ax(sing_def), sing_def, got_eqs.sequent.right[0].right)
        got_eqs = mp(got_eqs, got_app_sing_ja_cja, Apply(sing, ja, cja), and_eqs)
        got_eq_ja = apply_thm(and_elim_left(eq_ja_ska, Eq(ca_new, cja), []), [],
            and_eqs, eq_ja_ska, got_eqs)
        # [...] |- Eq(ska, ja)

        # Eq(ska,ja) = ∀z.z∈ska ↔ z∈ja. So In(ja,ka) → transfer via Eq(ska,ja):
        # ∀z.z∈ska ↔ z∈ja → In(z,ska) ↔ In(z,ja). With z=ka: In(ka,ska) ↔ In(ka,ja).
        # Hmm, we need In(ska,ka), not In(ka,ska).
        # Actually, Eq(ska,ja) + In(ja,ka): since ja and ska are "the same set",
        # In(ja,ka) IS In(ska,ka) (by Eq transfer in the second arg of In).
        # Eq(ska,ja) → In(ja,ka) ↔ In(ska,ka)? No, that transfers the first arg of In.
        # Eq(ska,ja) = ∀z. z∈ska ↔ z∈ja. This is about ELEMENTS of ska vs ja.
        # For In(ja,ka) → In(ska,ka): we need to transfer the first arg of In.
        # That's Leibniz: Eq(ska,ja) via eq_substitution → In(ska,z) ↔ In(ja,z). Instantiate z=ka.
        from theorems.logic import eq_substitution
        es_thm = eq_substitution()
        iff_in_ka = Iff(In(ska, ka), In(ja, ka))
        got_iff_inka = apply_thm(es_thm, [ska, ja, ka], eq_ja_ska, iff_in_ka, got_eq_ja)
        got_back_in = apply_thm(iff_mp_rev(In(ska,ka), In(ja,ka), []), [],
            iff_in_ka, Implies(In(ja,ka), In(ska,ka)), got_iff_inka)
        got_in_ska_ka = mp(got_back_in, ax(In(ja,ka)), In(ja,ka), In(ska,ka))

        got_bot = bot_from_in_ska_ka(got_in_ska_ka)
        return Proof(Sequent(got_bot.sequent.left, [target]),
            'weakening_right', [got_bot], principal=target)

    # === 2. Function(tra_new) via extend_function ===
    ef = extend_function()
    func_trn = FuncDef(tra_new)
    # Consistency: ∀zv. Apply(tra,ska,zv) → Eq(ca_new,zv)
    # Apply(tra,ska,zv) → ⊥ (via bot_from_in_ska_ka pattern: Apply gives ∃p.OrdPair∧In,
    # but we need In(ska,ka) which requires knowing tra's domain ⊆ {0..ka}).
    # Simpler: Apply(tra,ska,zv) + singleton_apply_eq on... no, that's for sing.
    # Actually, we can prove consistency vacuously: from Apply(tra,ska,zv), derive ⊥,
    # then weaken to Eq(ca_new,zv). Apply(tra,ska,zv) doesn't directly give In(ska,ka).
    # But with Function(tra) + Apply(tra,ka,ca): if also Apply(tra,ska,zv), we'd need ska≠ka,
    # which we have (ska=S(ka), so Eq(ska,ka) → In(ka,ka) → ⊥).
    # BUT: Apply(tra,ska,zv) doesn't mean ska is in the DOMAIN of tra in a simple way.
    # It means ∃p. OrdPair(p,ska,zv) ∧ In(p,tra). This doesn't directly give In(ska,ka).
    #
    # Prove consistency from dom_bound + omega context:
    # dom_bound: ∀x,y. Apply(tra,x,y) → Or(In(x,ka), Eq(x,ka))
    from core.derived import Or
    xd, yd = Var(postfix='xd'), Var(postfix='yd')
    dom_bound = Forall(xd, Forall(yd, Implies(Apply(tra, xd, yd),
        Or(In(xd, ka), Eq(xd, ka)))))
    zv = Var(postfix='zv')
    app_tra_ska_zv = Apply(tra, ska, zv)
    eq_cn_zv = Eq(ca_new, zv)
    consist = Forall(zv, Implies(app_tra_ska_zv, eq_cn_zv))

    # From dom_bound instantiated with x=ska, y=zv:
    # Apply(tra,ska,zv) → Or(In(ska,ka), Eq(ska,ka))
    or_ska = Or(In(ska, ka), Eq(ska, ka))
    got_dom_inst = apply_thm(ax(dom_bound), [ska, zv], app_tra_ska_zv, or_ska, ax(app_tra_ska_zv))
    # [dom_bound, Apply(tra,ska,zv)] |- Or(In(ska,ka), Eq(ska,ka))

    # Both disjuncts → ⊥ → Eq(ca_new,zv)
    # In(ska,ka) case: bot_from_in_ska_ka
    got_bot_left_d = bot_from_in_ska_ka(ax(In(ska, ka)))
    got_left_d = Proof(Sequent(got_bot_left_d.sequent.left, [eq_cn_zv]),
        'weakening_right', [got_bot_left_d], principal=eq_cn_zv)

    # Eq(ska,ka) case: ka∈ska (from Successor) + Eq(ska,ka) → ka∈ka → ⊥
    # Reuse bot_from_sing_apply pattern: Eq(ska,ka) → eq_substitution → In(ka,ska)→In(ka,ka)
    # Actually simpler: Eq(ska,ka) = ∀z. z∈ska ↔ z∈ka. Instantiate z=ka.
    # Forward: ka∈ska → ka∈ka. ka∈ska from Successor. So ka∈ka. Then ⊥.
    from theorems.logic import eq_reflexive, or_intro_right as oir_thm
    er = eq_reflexive()
    # ka∈ska from Successor(ska,ka)
    eq_kaka = Eq(ka, ka)
    got_eq_kk = apply_thm(er, [ka], concl=eq_kaka)
    in_ka_ska_f = In(ka, ska)
    iff_ka_ska_d = Iff(in_ka_ska_f, Or(In(ka, ka), eq_kaka))
    got_or_kk = apply_thm(oir_thm(In(ka,ka), eq_kaka, []), [],
        eq_kaka, Or(In(ka,ka), eq_kaka), got_eq_kk)
    got_in_ka_ska_d = mp(apply_thm(iff_mp_rev(in_ka_ska_f, Or(In(ka,ka), eq_kaka), []),
        [], iff_ka_ska_d, Implies(Or(In(ka,ka), eq_kaka), in_ka_ska_f),
        fl(succ_ska, iff_ka_ska_d, ka)),
        got_or_kk, Or(In(ka,ka), eq_kaka), in_ka_ska_f)
    # [succ_ska] |- In(ka, ska)

    # Eq(ska,ka) → In(ka,ska) ↔ In(ka,ka). Forward: In(ka,ska)→In(ka,ka).
    iff_kk_d = Iff(In(ka, ska), In(ka, ka))
    got_iff_kk_d = apply_thm(ax(Eq(ska, ka)), [ka], concl=iff_kk_d)
    got_fwd_kk = apply_thm(iff_mp(In(ka,ska), In(ka,ka), []), [],
        iff_kk_d, Implies(In(ka,ska), In(ka,ka)), got_iff_kk_d)
    got_in_kk = mp(got_fwd_kk, got_in_ka_ska_d, In(ka,ska), In(ka,ka))
    # [Eq(ska,ka), succ_ska] |- In(ka,ka). Use omega_no_self_membership for ⊥.
    not_kk = Not(In(ka, ka))
    onsm2 = omega_no_self_membership()
    got_not_kk = apply_thm(onsm2, [w, ka])
    got_not_kk = mp(got_not_kk, ax(omega_w), omega_w, Implies(in_ka_w, not_kk))
    got_not_kk = mp(got_not_kk, ax(in_ka_w), in_ka_w, not_kk)
    got_in_kk_w = weaken_to(got_in_kk, list(got_not_kk.sequent.left))
    got_not_kk_w = weaken_to(got_not_kk, list(got_in_kk_w.sequent.left))
    ctx_r = list(got_in_kk_w.sequent.left)
    got_bot_r = Proof(Sequent(ctx_r + [not_kk], []), 'not_left', [got_in_kk_w], principal=not_kk)
    got_bot_r = Proof(Sequent(ctx_r, []), 'cut', [got_not_kk_w, got_bot_r], principal=not_kk)
    got_right_d = Proof(Sequent(ctx_r, [eq_cn_zv]), 'weakening_right', [got_bot_r], principal=eq_cn_zv)

    # or_elim
    oe_dom = or_elim(In(ska, ka), Eq(ska, ka), eq_cn_zv, [])
    imp_l_d = Implies(In(ska, ka), eq_cn_zv)
    imp_r_d = Implies(Eq(ska, ka), eq_cn_zv)
    got_imp_l_d = Proof(Sequent([f for f in got_left_d.sequent.left if not same(f, In(ska,ka))],
        [imp_l_d]), 'implies_right', [got_left_d], principal=imp_l_d)
    got_imp_r_d = Proof(Sequent([f for f in got_right_d.sequent.left if not same(f, Eq(ska,ka))],
        [imp_r_d]), 'implies_right', [got_right_d], principal=imp_r_d)
    got_consist_body = apply_thm(oe_dom, [], or_ska,
        Implies(imp_l_d, Implies(imp_r_d, eq_cn_zv)), got_dom_inst)
    got_consist_body = mp(got_consist_body, got_imp_l_d, imp_l_d, Implies(imp_r_d, eq_cn_zv))
    got_consist_body = mp(got_consist_body, got_imp_r_d, imp_r_d, eq_cn_zv)
    # [..., dom_bound, Apply(tra,ska,zv)] |- Eq(ca_new, zv)

    # Close: Apply → Eq, ∀zv = consist
    imp_consist = Implies(app_tra_ska_zv, eq_cn_zv)
    left_c = [f for f in got_consist_body.sequent.left if not same(f, app_tra_ska_zv)]
    got_consist = Proof(Sequent(left_c, [imp_consist]),
        'implies_right', [got_consist_body], principal=imp_consist)
    fa_consist = Forall(zv, imp_consist)
    got_consist = Proof(Sequent(got_consist.sequent.left, [fa_consist]),
        'forall_right', [got_consist], principal=fa_consist, term=zv)
    # [dom_bound, omega ctx] |- consist

    # Apply extend_function
    got_func_trn = apply_thm(ef, [tra, sing, pair_ska, ska, ca_new, tra_new])
    got_func_trn = mp(got_func_trn, ax(func_tra), func_tra, got_func_trn.sequent.right[0].right)
    got_func_trn = mp(got_func_trn, ax(op_pair_ska), op_pair_ska, got_func_trn.sequent.right[0].right)
    got_func_trn = mp(got_func_trn, ax(sing_def), sing_def, got_func_trn.sequent.right[0].right)
    got_func_trn = mp(got_func_trn, ax(union_def), union_def, got_func_trn.sequent.right[0].right)
    got_func_trn = mp(got_func_trn, got_consist, consist, func_trn)

    # === 3. Base ===
    z_prime = Var(postfix='zp2')
    app_tra_zp = Apply(tra, z_prime, c0)
    app_trn_zp = Apply(tra_new, z_prime, c0)
    got_app_old_z = apply_thm(ax(base_old), [z_prime], Empty(z_prime), app_tra_zp, ax(Empty(z_prime)))
    got_app_new_z = apply_thm(aul, [tra_new, tra, sing, z_prime, c0])
    got_app_new_z = mp(got_app_new_z, ax(union_def), union_def, Implies(app_tra_zp, app_trn_zp))
    got_app_new_z = mp(got_app_new_z, got_app_old_z, app_tra_zp, app_trn_zp)
    imp_base = Implies(Empty(z_prime), app_trn_zp)
    left_base = [f for f in got_app_new_z.sequent.left if not same(f, Empty(z_prime))]
    got_base = Proof(Sequent(left_base, [imp_base]), 'implies_right', [got_app_new_z], principal=imp_base)
    fa_base = Forall(z_prime, imp_base)
    got_base = Proof(Sequent(got_base.sequent.left, [fa_base]), 'forall_right', [got_base], principal=fa_base, term=z_prime)

    # === 4. Head ===
    asn = apply_singleton()
    app_sing_ska = Apply(sing, ska, ca_new)
    got_app_sing = apply_thm(asn, [ska, ca_new, pair_ska, sing])
    got_app_sing = mp(got_app_sing, ax(op_pair_ska), op_pair_ska, Implies(sing_def, app_sing_ska))
    got_app_sing = mp(got_app_sing, ax(sing_def), sing_def, app_sing_ska)
    app_trn_ska = Apply(tra_new, ska, ca_new)
    got_head = apply_thm(aur, [tra_new, tra, sing, ska, ca_new])
    got_head = mp(got_head, ax(union_def), union_def, Implies(app_sing_ska, app_trn_ska))
    got_head = mp(got_head, got_app_sing, app_sing_ska, app_trn_ska)

    # === 5. step_valid ===
    app_trn_ja = Apply(tra_new, ja, cja)
    app_trn_sja = Apply(tra_new, sja, cja1)
    step_body_inner = Exists(cja1, And(app_trn_sja, TMStep(delta, cja, cja1)))
    iff_ska_ja = Iff(In(ja, ska), Or(In(ja, ka), Eq(ja, ka)))
    got_or_ja = mp(apply_thm(iff_mp(In(ja,ska), Or(In(ja,ka), Eq(ja,ka)), []),
        [], iff_ska_ja, Implies(In(ja,ska), Or(In(ja,ka), Eq(ja,ka))),
        fl(succ_ska, iff_ska_ja, ja)),
        ax(In(ja, ska)), In(ja, ska), Or(In(ja, ka), Eq(ja, ka)))

    aue = apply_union_elim()
    app_tra_ja = Apply(tra, ja, cja)
    app_sing_ja = Apply(sing, ja, cja)
    or_apps = Or(app_tra_ja, app_sing_ja)
    got_or_apps = apply_thm(aue, [tra_new, tra, sing, ja, cja])
    got_or_apps = mp(got_or_apps, ax(union_def), union_def, Implies(app_trn_ja, or_apps))
    got_or_apps = mp(got_or_apps, ax(app_trn_ja), app_trn_ja, or_apps)

    # In(ja,ka) + Apply(tra,ja,cja): old step_valid + transfer
    got_old_sv = apply_thm(ax(step_valid_old), [ja], In(ja,ka),
        Forall(sja, Implies(Successor(sja,ja), Forall(cja, Implies(app_tra_ja,
            Exists(cja1, And(Apply(tra, sja, cja1), TMStep(delta, cja, cja1))))))),
        ax(In(ja, ka)))
    got_old_sv = apply_thm(got_old_sv, [sja], Successor(sja,ja),
        Forall(cja, Implies(app_tra_ja, Exists(cja1, And(Apply(tra, sja, cja1), TMStep(delta, cja, cja1))))),
        ax(Successor(sja, ja)))
    got_old_sv = apply_thm(got_old_sv, [cja], app_tra_ja,
        Exists(cja1, And(Apply(tra, sja, cja1), TMStep(delta, cja, cja1))), ax(app_tra_ja))

    app_tra_sja = Apply(tra, sja, cja1)
    and_old = And(app_tra_sja, TMStep(delta, cja, cja1))
    got_app_tra_sja = apply_thm(and_elim_left(app_tra_sja, TMStep(delta, cja, cja1), []),
        [], and_old, app_tra_sja, ax(and_old))
    got_tmstep_old = apply_thm(and_elim_right(app_tra_sja, TMStep(delta, cja, cja1), []),
        [], and_old, TMStep(delta, cja, cja1), ax(and_old))
    got_app_trn_sja_t = apply_thm(aul, [tra_new, tra, sing, sja, cja1])
    got_app_trn_sja_t = mp(got_app_trn_sja_t, ax(union_def), union_def, Implies(app_tra_sja, app_trn_sja))
    got_app_trn_sja_t = mp(got_app_trn_sja_t, got_app_tra_sja, app_tra_sja, app_trn_sja)

    def mk_and(got_l, got_r):
        L, R = got_l.sequent.right[0], got_r.sequent.right[0]
        return mp(apply_thm(and_intro(L, R, []), [], L, Implies(R, And(L, R)), got_l), got_r, R, And(L, R))

    got_and_new = mk_and(got_app_trn_sja_t, got_tmstep_old)
    got_ex_new = eir(got_and_new, And(app_trn_sja, TMStep(delta, cja, cja1)), cja1, cja1)
    got_ex_new = eel(got_ex_new, and_old, cja1)
    got_case_in_tra = cut(got_ex_new, Exists(cja1, and_old), got_old_sv)

    # In(ja,ka) + Apply(sing,ja,cja): bot via omega
    got_case_in_sing = bot_from_sing_apply(ax(app_sing_ja), step_body_inner)
    got_case_in_sing = wl(got_case_in_sing, In(ja, ka), Successor(sja, ja))

    # or_elim on Apply sub-cases
    oe_apps = or_elim(app_tra_ja, app_sing_ja, step_body_inner, [])
    got_imp_tra = Proof(Sequent([f for f in got_case_in_tra.sequent.left if not same(f, app_tra_ja)],
        [Implies(app_tra_ja, step_body_inner)]), 'implies_right', [got_case_in_tra],
        principal=Implies(app_tra_ja, step_body_inner))
    got_imp_sing = Proof(Sequent([f for f in got_case_in_sing.sequent.left if not same(f, app_sing_ja)],
        [Implies(app_sing_ja, step_body_inner)]), 'implies_right', [got_case_in_sing],
        principal=Implies(app_sing_ja, step_body_inner))
    got_case_in = apply_thm(oe_apps, [], or_apps,
        Implies(Implies(app_tra_ja, step_body_inner), Implies(Implies(app_sing_ja, step_body_inner), step_body_inner)),
        got_or_apps)
    got_case_in = mp(got_case_in, got_imp_tra, Implies(app_tra_ja, step_body_inner),
        Implies(Implies(app_sing_ja, step_body_inner), step_body_inner))
    got_case_in = mp(got_case_in, got_imp_sing, Implies(app_sing_ja, step_body_inner), step_body_inner)

    # Eq(ja,ka) case: placeholder (needs func_unique + TMStep transfer)
    # --- Eq(ja,ka) case: union_elim + func_unique + TMStep transfer ---
    # Apply(tra_new,ja,cja) → Or(Apply(tra,ja,cja), Apply(sing,ja,cja))
    # Apply(sing,...) sub-case: singleton_apply_eq → Eq(ja,ska) + Eq(ja,ka) → Eq(ka,ska) → ⊥
    # Apply(tra,...) sub-case: func_unique → Eq(cja,ca), build step from TMStep(delta,ca,ca_new)

    # Apply(sing,ja,cja) sub-case for Eq(ja,ka):
    # singleton_apply_eq → Eq(ska,ja). Eq(ja,ka) reversed → Eq(ka,ja).
    # eq_transitive(ka,ja,ska)... no, we have Eq(ska,ja) and Eq(ka,ja).
    # eq_symmetric(ska,ja) → Eq(ja,ska). eq_symmetric(ja,ka) → Eq(ka,ja).
    # eq_transitive(ka,ja,ska): Eq(ka,ja) + Eq(ja,ska) → Eq(ka,ska).
    # Then: Eq(ka,ska) = ∀z.z∈ka↔z∈ska. With ka∈ska (from Successor): ka∈ka → ⊥.
    from theorems.logic import eq_transitive
    from theorems.sets import ordpair_val_transfer, unique_successor
    from theorems.recursion import singleton_apply_eq as sae_thm, eq_apply_transfer
    et = eq_transitive()
    es = eq_symmetric()
    sae = sae_thm()
    eat = eq_apply_transfer()
    ovt = ordpair_val_transfer()
    us = unique_successor()

    # Build: [Apply(sing,ja,cja), Eq(ja,ka), Succ(sja,ja), omega ctx] |- step_body_inner
    eq_ska_ja = Eq(ska, ja)
    and_sae = And(eq_ska_ja, Eq(ca_new, cja))
    got_sae_eq = apply_thm(sae, [ska, ca_new, pair_ska, sing, ja, cja])
    got_sae_eq = mp(got_sae_eq, ax(op_pair_ska), op_pair_ska, got_sae_eq.sequent.right[0].right)
    got_sae_eq = mp(got_sae_eq, ax(sing_def), sing_def, got_sae_eq.sequent.right[0].right)
    got_sae_eq = mp(got_sae_eq, ax(app_sing_ja), app_sing_ja, and_sae)
    got_eq_ska_ja = apply_thm(and_elim_left(eq_ska_ja, Eq(ca_new, cja), []), [],
        and_sae, eq_ska_ja, got_sae_eq)
    # Eq(ja,ska) from Eq(ska,ja)
    eq_ja_ska = Eq(ja, ska)
    got_eq_ja_ska = apply_thm(es, [ska, ja], eq_ska_ja, eq_ja_ska, got_eq_ska_ja)
    # Eq(ka,ja) from Eq(ja,ka)
    eq_ka_ja = Eq(ka, ja)
    got_eq_ka_ja = apply_thm(es, [ja, ka], Eq(ja, ka), eq_ka_ja, ax(Eq(ja, ka)))
    # Eq(ka,ska) via eq_transitive
    eq_ka_ska = Eq(ka, ska)
    got_eq_ka_ska = apply_thm(et, [ka, ja, ska])
    got_eq_ka_ska = mp(got_eq_ka_ska, got_eq_ka_ja, eq_ka_ja, Implies(eq_ja_ska, eq_ka_ska))
    got_eq_ka_ska = mp(got_eq_ka_ska, got_eq_ja_ska, eq_ja_ska, eq_ka_ska)
    # Eq(ka,ska) → ka∈ska ↔ ka∈ka → ka∈ka → ⊥ (same pattern as bot_from_in_ska_ka)
    # Actually: Eq(ka,ska) = ∀z. z∈ka ↔ z∈ska. Use this to transfer ka∈ska → ka∈ka.
    from theorems.logic import eq_reflexive, or_intro_right
    er = eq_reflexive()
    eq_kaka = Eq(ka, ka)
    got_eq_kk = apply_thm(er, [ka], concl=eq_kaka)
    in_ka_ska = In(ka, ska)
    iff_ka_ska2 = Iff(in_ka_ska, Or(In(ka, ka), eq_kaka))
    got_or_kk = apply_thm(or_intro_right(In(ka,ka), eq_kaka, []), [],
        eq_kaka, Or(In(ka,ka), eq_kaka), got_eq_kk)
    got_in_ka_ska = mp(apply_thm(iff_mp_rev(in_ka_ska, Or(In(ka,ka), eq_kaka), []),
        [], iff_ka_ska2, Implies(Or(In(ka,ka), eq_kaka), in_ka_ska),
        fl(succ_ska, iff_ka_ska2, ka)),
        got_or_kk, Or(In(ka,ka), eq_kaka), in_ka_ska)
    # [...] |- In(ka, ska)
    # Transfer: Eq(ka,ska) → In(ka,ska) ↔ In(ka,ka). Forward direction.
    iff_kk = Iff(In(ka, ka), In(ka, ska))
    got_iff_kk = apply_thm(ax(eq_ka_ska), [ka], concl=iff_kk)
    got_in_ka_ka = mp(apply_thm(iff_mp_rev(In(ka,ka), In(ka,ska), []), [],
        iff_kk, Implies(In(ka,ska), In(ka,ka)), got_iff_kk),
        got_in_ka_ska, In(ka, ska), In(ka, ka))
    # [..., Eq(ka,ska)] |- In(ka, ka)
    got_in_ka_ka = cut(got_in_ka_ka, eq_ka_ska, got_eq_ka_ska)
    # omega_no_self_membership → ¬In(ka,ka)
    onsm = omega_no_self_membership()
    not_ka_ka = Not(In(ka, ka))
    got_not_kk = apply_thm(onsm, [w, ka])
    got_not_kk = mp(got_not_kk, ax(omega_w), omega_w, Implies(in_ka_w, not_ka_ka))
    got_not_kk = mp(got_not_kk, ax(in_ka_w), in_ka_w, not_ka_ka)
    # Contradiction → ⊥ → step_body_inner
    got_in_w = weaken_to(got_in_ka_ka, list(got_not_kk.sequent.left))
    got_not_w = weaken_to(got_not_kk, list(got_in_w.sequent.left))
    ctx_bot = list(got_in_w.sequent.left)
    got_bot_eq_sing = Proof(Sequent(ctx_bot + [not_ka_ka], []),
        'not_left', [got_in_w], principal=not_ka_ka)
    got_bot_eq_sing = Proof(Sequent(ctx_bot, []), 'cut',
        [got_not_w, got_bot_eq_sing], principal=not_ka_ka)
    got_case_eq_sing = Proof(Sequent(ctx_bot, [step_body_inner]),
        'weakening_right', [got_bot_eq_sing], principal=step_body_inner)
    got_case_eq_sing = wl(got_case_eq_sing, Eq(ja, ka), Successor(sja, ja))

    # Apply(tra,ja,cja) sub-case for Eq(ja,ka):
    # Eq(ja,ka) + Apply(tra,ja,cja) → Apply(tra,ka,cja) → func_unique → Eq(cja,ca)
    app_tra_ka_cja = Apply(tra, ka, cja)
    got_app_ka_cja = mp(apply_thm(eat, [tra, ja, ka, cja], Eq(ja,ka),
        Implies(app_tra_ja, app_tra_ka_cja), ax(Eq(ja,ka))),
        ax(app_tra_ja), app_tra_ja, app_tra_ka_cja)

    eq_cja_ca = Eq(cja, ca)
    fu = func_unique_thm()
    got_eq_cja = apply_thm(fu, [tra, ka, cja, ca])
    got_eq_cja = mp(got_eq_cja, ax(func_tra), func_tra, got_eq_cja.sequent.right[0].right)
    got_eq_cja = mp(got_eq_cja, got_app_ka_cja, app_tra_ka_cja, got_eq_cja.sequent.right[0].right)
    got_eq_cja = mp(got_eq_cja, ax(app_tra_ka_ca), app_tra_ka_ca, eq_cja_ca)
    # [..., Eq(ja,ka), Apply(tra,ja,cja)] |- Eq(cja, ca)

    # Eq(sja,ska) from Succ(sja,ja) + Succ(ska,ka) + Eq(ja,ka) via Extensionality.
    # Same pattern as headmove_right_elim: iff_chain on Successor bodies.
    from theorems.logic import iff_chain, iff_sym, or_iff_compat
    from theorems.sets import eq_in_eq
    zz = Var(postfix='zz2')
    iff_sja = Iff(In(zz, sja), Or(In(zz, ja), Eq(zz, ja)))
    got_iff_sja = apply_thm(ax(Successor(sja, ja)), [zz], concl=iff_sja)
    iff_ska2 = Iff(In(zz, ska), Or(In(zz, ka), Eq(zz, ka)))
    got_iff_ska2 = apply_thm(ax(succ_ska), [zz], concl=iff_ska2)
    # Eq(ja,ka) → Iff(In(zz,ja), In(zz,ka)) + Iff(Eq(zz,ja), Eq(zz,ka))
    got_iff_in_jk = apply_thm(ax(Eq(ja,ka)), [zz],
        concl=Iff(In(zz,ja), In(zz,ka)))
    eie = eq_in_eq()
    got_eie = apply_thm(eie, [ja, ka], Eq(ja,ka),
        Forall(zz, Iff(Eq(zz,ja), Eq(zz,ka))), ax(Eq(ja,ka)))
    got_iff_eq_jk = apply_thm(got_eie, [zz], concl=Iff(Eq(zz,ja), Eq(zz,ka)))
    oic = or_iff_compat(In(zz,ja), Eq(zz,ja), In(zz,ka), Eq(zz,ka), [])
    got_iff_or = mp(apply_thm(oic, [], got_iff_in_jk.sequent.right[0],
        Implies(got_iff_eq_jk.sequent.right[0], Iff(Or(In(zz,ja),Eq(zz,ja)), Or(In(zz,ka),Eq(zz,ka)))),
        got_iff_in_jk),
        got_iff_eq_jk, got_iff_eq_jk.sequent.right[0],
        Iff(Or(In(zz,ja),Eq(zz,ja)), Or(In(zz,ka),Eq(zz,ka))))
    # Chain: In(zz,sja) ↔ Or(...ja...) ↔ Or(...ka...) ↔ In(zz,ska)
    ic1 = iff_chain(In(zz,sja), Or(In(zz,ja),Eq(zz,ja)), Or(In(zz,ka),Eq(zz,ka)), [])
    got_iff_1 = mp(apply_thm(ic1, [], iff_sja,
        Implies(got_iff_or.sequent.right[0], Iff(In(zz,sja), Or(In(zz,ka),Eq(zz,ka)))),
        got_iff_sja), got_iff_or, got_iff_or.sequent.right[0],
        Iff(In(zz,sja), Or(In(zz,ka),Eq(zz,ka))))
    isym = iff_sym(In(zz,ska), Or(In(zz,ka),Eq(zz,ka)), [])
    got_iff_ska_rev = apply_thm(isym, [], iff_ska2,
        Iff(Or(In(zz,ka),Eq(zz,ka)), In(zz,ska)), got_iff_ska2)
    ic2 = iff_chain(In(zz,sja), Or(In(zz,ka),Eq(zz,ka)), In(zz,ska), [])
    got_iff_sja_ska = mp(apply_thm(ic2, [], got_iff_1.sequent.right[0],
        Implies(got_iff_ska_rev.sequent.right[0], Iff(In(zz,sja), In(zz,ska))),
        got_iff_1), got_iff_ska_rev, got_iff_ska_rev.sequent.right[0],
        Iff(In(zz,sja), In(zz,ska)))
    fa_iff_sja_ska = Forall(zz, Iff(In(zz,sja), In(zz,ska)))
    got_fa_sja_ska = Proof(Sequent(got_iff_sja_ska.sequent.left, [fa_iff_sja_ska]),
        'forall_right', [got_iff_sja_ska], principal=fa_iff_sja_ska, term=zz)
    eq_sja_ska = Eq(sja, ska)  # = ∀z. z∈sja ↔ z∈ska = fa_iff_sja_ska
    # got_fa_sja_ska IS Eq(sja,ska) by definition
    got_eq_sja_ska = got_fa_sja_ska

    # Apply(tra_new,sja,ca_new) from Apply(tra_new,ska,ca_new) + Eq(ska,sja)
    eq_ska_sja = Eq(ska, sja)
    got_eq_ska_sja = apply_thm(es, [sja, ska], eq_sja_ska, eq_ska_sja, got_eq_sja_ska)
    app_trn_sja_can = Apply(tra_new, sja, ca_new)
    got_app_trn_sja_eq = mp(apply_thm(eat, [tra_new, ska, sja, ca_new], eq_ska_sja,
        Implies(app_trn_ska, app_trn_sja_can), got_eq_ska_sja),
        got_head, app_trn_ska, app_trn_sja_can)

    # TMStep(delta,cja,ca_new) from TMStep(delta,ca,ca_new) + Eq(cja,ca)
    # TMStep expands to ∀9vars. Config(before,...) → rest.
    # With Eq(cja,ca): Config(cja,...) → Config(ca,...) via ordpair_set_transfer on the inner OrdPair.
    # Open TMStep(delta,ca,ca_new)'s foralls, derive body with Config(cja,...) as hypothesis.
    from theorems.sets import ordpair_set_transfer
    ost = ordpair_set_transfer()
    tmstep_cja = TMStep(delta, cja, ca_new)
    # Instead of opening 9 foralls inline (very verbose), use apply_func_transfer:
    # Eq(cja,ca) means same elements. TMStep(delta,x,ca_new) after expansion uses In(p,x).
    # apply_func_transfer: Eq(f,g) → Apply(f,...) → Apply(g,...) — but for TMStep not Apply.
    # TMStep is NOT Apply. It's a definition that expands to Forall chain.
    # The transfer is about the .before arg which appears inside Config.
    # Config(x,q,h,tape) = ∀v. OrdPair(v,h,tape) → OrdPair(x,q,v). x appears in OrdPair.
    # OrdPair(x,...) uses In(elements, x) via Singleton/PairSet definitions.
    # With Eq(cja,ca): every In(p,cja) ↔ In(p,ca). So OrdPair(cja,...) ↔ OrdPair(ca,...).
    # Same() will NOT match TMStep(delta,cja,...) with TMStep(delta,ca,...).
    # We need a proof transfer.
    #
    # Shortcut: Eq(cja,ca) → TMStep(delta,ca,ca_new) → TMStep(delta,cja,ca_new)
    # This is: apply_func_transfer on the "set" position of TMStep?
    # TMStep(delta,x,y) when expanded has In(p,x) in the Config part.
    # apply_func_transfer transfers Apply's function position, not TMStep's.
    #
    # SIMPLEST: just use the Eq to note that TMStep(delta,cja,ca_new) and TMStep(delta,ca,ca_new)
    # have the same expansion modulo Eq. The engine checks via same() after _expand.
    # But same() uses structural + alpha-equiv, not Eq-equiv. So they won't match.
    #
    # ACTUAL IMPLEMENTATION: Eq(cja,ca) means ∀z. z∈cja ↔ z∈ca.
    # TMStep(delta,ca,ca_new) after expansion: ∀q,h,tape,...
    #   (∀v. OrdPair(v,h,tape) → OrdPair(ca,q,v)) → ... → (∀v. OrdPair(v,...) → OrdPair(ca_new,qn,v))
    # TMStep(delta,cja,ca_new): same but OrdPair(cja,q,v) instead of OrdPair(ca,q,v).
    # OrdPair(x,q,v) = ∀d. In(d,x) ↔ Or(Eq(d,{q}), Eq(d,{q,v})).
    # With Eq(cja,ca): In(d,cja) ↔ In(d,ca). So OrdPair(cja,...) ↔ OrdPair(ca,...).
    #
    # This transfer needs:
    # 1. Instantiate TMStep(delta,ca,ca_new) with 9 vars → Body(ca).
    # 2. Assume Config(cja,q,h,tape) on left.
    # 3. Derive Config(ca,q,h,tape) from it + Eq(cja,ca).
    #    Config(cja,...) instantiate v: OrdPair(v,h,tape) → OrdPair(cja,q,v).
    #    ordpair_set_transfer: Eq(ca,cja) → OrdPair(cja,q,v) → OrdPair(ca,q,v).
    #    Chain: OrdPair(v,h,tape) → OrdPair(ca,q,v). Close ∀v → Config(ca,...).
    # 4. mp with Body(ca) → rest.
    # 5. Discharge Config(cja,...), close 9 foralls → TMStep(delta,cja,ca_new).
    #
    # This IS the proper proof. ~20 lines. Let me inline it.

    eq_ca_cja = Eq(ca, cja)
    got_eq_ca_cja = apply_thm(es, [cja, ca], eq_cja_ca, eq_ca_cja, got_eq_cja)

    # Open TMStep(delta,ca,ca_new) with 9 fresh vars
    sq, sh, st, ss = Var(postfix='sq2'), Var(postfix='sh2'), Var(postfix='st2'), Var(postfix='ss2')
    sw, sd, sqn, shn, stn = Var(postfix='sw2'), Var(postfix='sd2'), Var(postfix='sqn2'), Var(postfix='shn2'), Var(postfix='stn2')
    cfg_ca_inner = TMConfig(ca, sq, sh, st)
    cfg_cja_inner = TMConfig(cja, sq, sh, st)
    app_read = Apply(st, sh, ss)
    trans_inner = TMTransition(delta, sq, ss, sw, sd, sqn)
    upd_inner = TapeUpdate(stn, st, sh, sw)
    move_inner = HeadMove(sh, shn, sd)
    cfg_new_inner = TMConfig(ca_new, sqn, shn, stn)
    rest_inner = Implies(app_read, Implies(trans_inner, Implies(upd_inner,
        Implies(move_inner, cfg_new_inner))))

    # TMStep(delta,ca,ca_new) instantiated → Config(ca,...) → rest
    got_tmstep_inst = apply_thm(ax(tmstep_ca), [sq, sh, st, ss, sw, sd, sqn, shn, stn])
    # [tmstep_ca] |- Config(ca,sq,sh,st) → rest_inner
    # Actually after instantiation it's the Implies chain. Let me use mp to peel Config.
    while type(got_tmstep_inst.sequent.right[0]).__name__ == 'Implies':
        cur = got_tmstep_inst.sequent.right[0]
        if same(cur.left, cfg_ca_inner):
            break
        got_tmstep_inst = mp(got_tmstep_inst, ax(cur.left), cur.left, cur.right)
    # Hmm, this won't work because Config is the FIRST premise.
    # After 9 foralls, the body is: Config(ca,...) → Apply → Trans → TapeUpdate → HeadMove → Config(ca_new,...)
    # So the first Implies has Config(ca,...) on the left.

    # Config(cja,...) → Config(ca,...) via ordpair_set_transfer + Eq(ca,cja)
    vv = Var(postfix='vv2')
    op_vv = OrdPair(vv, sh, st)
    op_cja_vv = OrdPair(cja, sq, vv)
    op_ca_vv = OrdPair(ca, sq, vv)
    # Config(cja,...) instantiate vv: OrdPair(vv,sh,st) → OrdPair(cja,sq,vv)
    got_cfg_cja_inst = apply_thm(ax(cfg_cja_inner), [vv], op_vv, op_cja_vv, ax(op_vv))
    # ordpair_set_transfer: Eq(ca,cja) → OrdPair(cja,sq,vv) → OrdPair(ca,sq,vv)
    got_op_ca_vv = mp(apply_thm(ost, [ca, cja, sq, vv], eq_ca_cja,
        Implies(op_cja_vv, op_ca_vv), got_eq_ca_cja),
        got_cfg_cja_inst, op_cja_vv, op_ca_vv)
    # [cfg_cja_inner, OrdPair(vv,sh,st), Eq(cja,ca), ...] |- OrdPair(ca,sq,vv)
    # Discharge OrdPair(vv,...), close ∀vv → Config(ca,...)
    imp_vv = Implies(op_vv, op_ca_vv)
    left_vv = [f for f in got_op_ca_vv.sequent.left if not same(f, op_vv)]
    got_cfg_ca_from_cja = Proof(Sequent(left_vv, [imp_vv]),
        'implies_right', [got_op_ca_vv], principal=imp_vv)
    fa_vv = Forall(vv, imp_vv)
    got_cfg_ca_from_cja = Proof(Sequent(got_cfg_ca_from_cja.sequent.left, [fa_vv]),
        'forall_right', [got_cfg_ca_from_cja], principal=fa_vv, term=vv)
    # [cfg_cja_inner, Eq(cja,ca), ...] |- Config(ca,sq,sh,st)

    # mp with TMStep body: Config(ca,...) → rest → rest from Config(cja,...) + Eq
    got_rest = mp(got_tmstep_inst, got_cfg_ca_from_cja, cfg_ca_inner, rest_inner)
    # Peel remaining premises via ax
    while type(got_rest.sequent.right[0]).__name__ == 'Implies':
        cur = got_rest.sequent.right[0]
        got_rest = mp(got_rest, ax(cur.left), cur.left, cur.right)
    # [..., cfg_cja_inner, app_read, trans_inner, upd_inner, move_inner] |- cfg_new_inner

    # Discharge all 5 TMStep premises + close 9 foralls → TMStep(delta,cja,ca_new)
    for premise in [move_inner, upd_inner, trans_inner, app_read, cfg_cja_inner]:
        imp2 = Implies(premise, got_rest.sequent.right[0])
        left2 = [f for f in got_rest.sequent.left if not same(f, premise)]
        got_rest = Proof(Sequent(left2, [imp2]), 'implies_right', [got_rest], principal=imp2)
    for v in [stn, shn, sqn, sd, sw, ss, st, sh, sq]:
        body2 = got_rest.sequent.right[0]
        fa2 = Forall(v, body2)
        got_rest = Proof(Sequent(got_rest.sequent.left, [fa2]),
            'forall_right', [got_rest], principal=fa2, term=v)
    got_tmstep_cja = got_rest
    # [..., Eq(cja,ca)] |- TMStep(delta,cja,ca_new)

    # Build And(Apply(tra_new,sja,ca_new), TMStep(delta,cja,ca_new))
    got_and_eq_case = mk_and(got_app_trn_sja_eq, got_tmstep_cja)
    # eir cja1 = ca_new
    got_ex_eq_case = eir(got_and_eq_case,
        And(Apply(tra_new, sja, cja1), TMStep(delta, cja, cja1)), cja1, ca_new)
    got_case_eq_tra = got_ex_eq_case
    # [..., Eq(ja,ka), Succ(sja,ja), Apply(tra,ja,cja)] |- step_body_inner

    # or_elim on Apply sub-cases for Eq(ja,ka):
    oe_apps_eq = or_elim(app_tra_ja, app_sing_ja, step_body_inner, [])
    got_imp_tra_eq = Proof(Sequent([f for f in got_case_eq_tra.sequent.left if not same(f, app_tra_ja)],
        [Implies(app_tra_ja, step_body_inner)]), 'implies_right', [got_case_eq_tra],
        principal=Implies(app_tra_ja, step_body_inner))
    got_imp_sing_eq = Proof(Sequent([f for f in got_case_eq_sing.sequent.left if not same(f, app_sing_ja)],
        [Implies(app_sing_ja, step_body_inner)]), 'implies_right', [got_case_eq_sing],
        principal=Implies(app_sing_ja, step_body_inner))
    # Need Or(Apply(tra,ja,cja), Apply(sing,ja,cja)) on the left — from union_elim on Apply(tra_new,ja,cja)
    got_case_eq = apply_thm(oe_apps_eq, [], or_apps,
        Implies(Implies(app_tra_ja, step_body_inner), Implies(Implies(app_sing_ja, step_body_inner), step_body_inner)),
        got_or_apps)
    got_case_eq = mp(got_case_eq, got_imp_tra_eq, Implies(app_tra_ja, step_body_inner),
        Implies(Implies(app_sing_ja, step_body_inner), step_body_inner))
    got_case_eq = mp(got_case_eq, got_imp_sing_eq, Implies(app_sing_ja, step_body_inner), step_body_inner)

    # or_elim on In(ja,ka) vs Eq(ja,ka)
    oe_ja = or_elim(In(ja, ka), Eq(ja, ka), step_body_inner, [])
    got_imp_in = Proof(Sequent([f for f in got_case_in.sequent.left if not same(f, In(ja, ka))],
        [Implies(In(ja, ka), step_body_inner)]), 'implies_right', [got_case_in],
        principal=Implies(In(ja, ka), step_body_inner))
    got_imp_eq = Proof(Sequent([f for f in got_case_eq.sequent.left if not same(f, Eq(ja, ka))],
        [Implies(Eq(ja, ka), step_body_inner)]), 'implies_right', [got_case_eq],
        principal=Implies(Eq(ja, ka), step_body_inner))
    got_sv_body = apply_thm(oe_ja, [], Or(In(ja,ka), Eq(ja,ka)),
        Implies(Implies(In(ja,ka), step_body_inner), Implies(Implies(Eq(ja,ka), step_body_inner), step_body_inner)),
        got_or_ja)
    got_sv_body = mp(got_sv_body, got_imp_in, Implies(In(ja,ka), step_body_inner),
        Implies(Implies(Eq(ja,ka), step_body_inner), step_body_inner))
    got_sv_body = mp(got_sv_body, got_imp_eq, Implies(Eq(ja,ka), step_body_inner), step_body_inner)

    for premise, var in [(app_trn_ja, cja), (Successor(sja, ja), sja), (In(ja, ska), ja)]:
        imp = Implies(premise, got_sv_body.sequent.right[0])
        left = [f for f in got_sv_body.sequent.left if not same(f, premise)]
        got_sv_body = Proof(Sequent(left, [imp]), 'implies_right', [got_sv_body], principal=imp)
        fa = Forall(var, got_sv_body.sequent.right[0])
        got_sv_body = Proof(Sequent(got_sv_body.sequent.left, [fa]), 'forall_right', [got_sv_body], principal=fa, term=var)
    got_sv = got_sv_body

    # === 6. Domain bound for tra_new ===
    # Old: ∀x,y. Apply(tra,x,y) → Or(In(x,ka), Eq(x,ka)) — domain ⊆ S(ka)
    # New: ∀x,y. Apply(tra_new,x,y) → Or(In(x,ska), Eq(x,ska)) — domain ⊆ S(S(ka))
    # union_elim: Apply(tra_new,x,y) → Or(Apply(tra,x,y), Apply(sing,x,y))
    # Apply(tra,x,y): old dom_bound → Or(In(x,ka),Eq(x,ka)).
    #   In(x,ka) → In(x,ska) from Successor(ska,ka) backward.
    #   Eq(x,ka) → In(x,ska) from Successor(ska,ka) backward (ka ∈ S(ka)).
    #   So Or(In(x,ka),Eq(x,ka)) → In(x,ska) → Or(In(x,ska),Eq(x,ska)).
    # Apply(sing,x,y): singleton_apply_eq → Eq(ska,x) → Eq(x,ska) → Or(In(x,ska),Eq(x,ska)).
    from theorems.logic import or_intro_left as oil_thm
    xdn = Var(postfix='xdn')
    ydn = Var(postfix='ydn')
    app_trn_xdn = Apply(tra_new, xdn, ydn)
    or_dom_new = Or(In(xdn, ska), Eq(xdn, ska))

    # Apply(tra,xdn,ydn) case: old dom_bound → Or(In(xdn,ka),Eq(xdn,ka))
    app_tra_xdn = Apply(tra, xdn, ydn)
    or_dom_old = Or(In(xdn, ka), Eq(xdn, ka))
    got_dom_old = apply_thm(ax(dom_bound), [xdn, ydn], app_tra_xdn, or_dom_old, ax(app_tra_xdn))
    # Or(In(xdn,ka),Eq(xdn,ka)) → In(xdn,ska) from Successor backward
    # Successor(ska,ka): ∀z. In(z,ska) ↔ Or(In(z,ka),Eq(z,ka)). Reverse: Or→In(z,ska).
    iff_succ_xdn = Iff(In(xdn, ska), Or(In(xdn, ka), Eq(xdn, ka)))
    got_in_ska = mp(apply_thm(iff_mp_rev(In(xdn, ska), or_dom_old, []),
        [], iff_succ_xdn, Implies(or_dom_old, In(xdn, ska)),
        fl(succ_ska, iff_succ_xdn, xdn)),
        got_dom_old, or_dom_old, In(xdn, ska))
    # [dom_bound, Apply(tra,xdn,ydn), succ_ska] |- In(xdn,ska)
    got_or_dom_tra = apply_thm(oil_thm(In(xdn,ska), Eq(xdn,ska), []), [],
        In(xdn, ska), or_dom_new, got_in_ska)

    # Apply(sing,xdn,ydn) case: singleton_apply_eq → Eq(ska,xdn) → Eq(xdn,ska)
    app_sing_xdn = Apply(sing, xdn, ydn)
    sae2 = singleton_apply_eq()
    eq_ska_xdn = Eq(ska, xdn)
    and_sae2 = And(eq_ska_xdn, Eq(ca_new, ydn))
    got_sae2 = apply_thm(sae2, [ska, ca_new, pair_ska, sing, xdn, ydn])
    got_sae2 = mp(got_sae2, ax(op_pair_ska), op_pair_ska, got_sae2.sequent.right[0].right)
    got_sae2 = mp(got_sae2, ax(sing_def), sing_def, got_sae2.sequent.right[0].right)
    got_sae2 = mp(got_sae2, ax(app_sing_xdn), app_sing_xdn, and_sae2)
    got_eq_ska_xdn = apply_thm(and_elim_left(eq_ska_xdn, Eq(ca_new,ydn), []), [],
        and_sae2, eq_ska_xdn, got_sae2)
    from theorems.logic import eq_symmetric as es_thm2
    es2 = es_thm2()
    eq_xdn_ska = Eq(xdn, ska)
    got_eq_xdn_ska = mp(apply_thm(es2, [ska, xdn]), got_eq_ska_xdn, eq_ska_xdn, eq_xdn_ska)
    from theorems.logic import or_intro_right as oir_thm2
    got_or_dom_sing = apply_thm(oir_thm2(In(xdn,ska), eq_xdn_ska, []), [],
        eq_xdn_ska, or_dom_new, got_eq_xdn_ska)

    # or_elim on Apply sub-cases
    or_apps_dom = Or(app_tra_xdn, app_sing_xdn)
    got_or_apps_dom = apply_thm(aue, [tra_new, tra, sing, xdn, ydn])
    got_or_apps_dom = mp(got_or_apps_dom, ax(union_def), union_def,
        Implies(app_trn_xdn, or_apps_dom))
    got_or_apps_dom = mp(got_or_apps_dom, ax(app_trn_xdn), app_trn_xdn, or_apps_dom)

    oe_dom = or_elim(app_tra_xdn, app_sing_xdn, or_dom_new, [])
    imp_tra_dom = Implies(app_tra_xdn, or_dom_new)
    imp_sing_dom = Implies(app_sing_xdn, or_dom_new)
    got_imp_tra_dom = Proof(Sequent(
        [f for f in got_or_dom_tra.sequent.left if not same(f, app_tra_xdn)],
        [imp_tra_dom]), 'implies_right', [got_or_dom_tra], principal=imp_tra_dom)
    got_imp_sing_dom = Proof(Sequent(
        [f for f in got_or_dom_sing.sequent.left if not same(f, app_sing_xdn)],
        [imp_sing_dom]), 'implies_right', [got_or_dom_sing], principal=imp_sing_dom)
    got_dom_body = apply_thm(oe_dom, [], or_apps_dom,
        Implies(imp_tra_dom, Implies(imp_sing_dom, or_dom_new)), got_or_apps_dom)
    got_dom_body = mp(got_dom_body, got_imp_tra_dom, imp_tra_dom, Implies(imp_sing_dom, or_dom_new))
    got_dom_body = mp(got_dom_body, got_imp_sing_dom, imp_sing_dom, or_dom_new)
    # Close: Apply(tra_new,xdn,ydn) → Or(...), ∀ydn, ∀xdn
    imp_dom_new = Implies(app_trn_xdn, or_dom_new)
    left_dom_new = [f for f in got_dom_body.sequent.left if not same(f, app_trn_xdn)]
    got_dom_new = Proof(Sequent(left_dom_new, [imp_dom_new]),
        'implies_right', [got_dom_body], principal=imp_dom_new)
    fa_ydn = Forall(ydn, imp_dom_new)
    got_dom_new = Proof(Sequent(got_dom_new.sequent.left, [fa_ydn]),
        'forall_right', [got_dom_new], principal=fa_ydn, term=ydn)
    fa_xdn = Forall(xdn, fa_ydn)
    got_dom_new = Proof(Sequent(got_dom_new.sequent.left, [fa_xdn]),
        'forall_right', [got_dom_new], principal=fa_xdn, term=xdn)

    # === 7. Compose + existentials ===
    got_hv = mk_and(got_head, got_sv)
    got_bhv = mk_and(got_base, got_hv)
    got_dbhv = mk_and(got_dom_new, got_bhv)    # insert dom_bound
    got_fbhv = mk_and(got_func_trn, got_dbhv)

    got_ex_trn = eir(got_fbhv, got_fbhv.sequent.right[0], tra_new, tra_new)
    got_ex_trn = eel(got_ex_trn, union_def, tra_new)
    got_ex_trn = cut(got_ex_trn, Exists(tra_new, union_def), got_ex_union)
    got_ex_trn = eel(got_ex_trn, sing_def, sing)
    got_ex_trn = cut(got_ex_trn, Exists(sing, sing_def), got_ex_sing)
    got_ex_trn = eel(got_ex_trn, op_pair_ska, pair_ska)
    got_ex_trn = cut(got_ex_trn, Exists(pair_ska, op_pair_ska), got_ex_pair)

    # Discharge hypotheses, close ∀
    proof = got_ex_trn
    xd = Var(postfix='xd'); yd = Var(postfix='yd')
    dom_bound_old = Forall(xd, Forall(yd, Implies(Apply(tra, xd, yd),
        Or(In(xd, ka), Eq(xd, ka)))))
    base_old_f = Forall(z, Implies(Empty(z), Apply(tra, z, c0)))
    step_valid_old_f = Forall(ja, Implies(In(ja, ka),
        Forall(sja, Implies(Successor(sja, ja),
            Forall(cja, Implies(Apply(tra, ja, cja),
                Exists(cja1, And(Apply(tra, sja, cja1), TMStep(delta, cja, cja1)))))))))
    hyps = [Apply(tra, ka, ca), tmstep_ca, step_valid_old_f, base_old_f,
            succ_ska, In(ka, w), Omega(w), dom_bound_old, FuncDef(tra)]
    for hyp in hyps:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [w, ca, delta, ka, c0, ca_new, ska, tra]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'phase1_step_extend_trace'
    return proof





def tape_read_sep():
    """|- ∀tape,a,b,zero. UnaryTape(tape,a,b) → Num(zero,0) → Apply(tape,a,zero)"""
    from tactics import apply_thm, mp, ax
    from core.proof import Proof, Sequent, same
    from theorems.logic import and_elim_left, and_elim_right
    from tm import UnaryTape

    tape, a, b, zero = Var(), Var(), Var(), Var()
    ut = UnaryTape(tape, a, b)
    num_zero = Num(zero, 0)
    app = Apply(tape, a, zero)

    exp = ut.expand()
    func_f = exp.left
    rest0 = exp.right
    low_f = rest0.left
    rest1 = rest0.right
    sep_f = rest1.left

    aer0 = and_elim_right(func_f, rest0, [])
    got_rest0 = apply_thm(aer0, [], ut, rest0, ax(ut))
    aer1 = and_elim_right(low_f, rest1, [])
    got_rest1 = apply_thm(aer1, [], rest0, rest1, got_rest0)
    ael1 = and_elim_left(sep_f, rest1.right, [])
    got_sep = apply_thm(ael1, [], rest1, sep_f, got_rest1)

    got = apply_thm(got_sep, [zero], num_zero, app, ax(num_zero))

    for premise in [num_zero, ut]:
        imp = Implies(premise, got.sequent.right[0])
        left = [f for f in got.sequent.left if not same(f, premise)]
        got = Proof(Sequent(left, [imp]), 'implies_right', [got], principal=imp)

    proof = got
    for v in [zero, b, a, tape]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'tape_read_sep'
    return proof


def tape_read_low():
    """Read from first group: UnaryTape + In(i,a) + Num(one,1) -> Apply(tape,i,one).
    |- forall tape, a, b, i, one.
         UnaryTape(tape,a,b) -> In(i,a) -> Num(one,1) -> Apply(tape,i,one)"""
    from tactics import apply_thm, mp, ax
    from core.proof import Proof, Sequent, same
    from theorems.logic import and_elim_left, and_elim_right
    from tm import UnaryTape

    tape, a, b, i, one = Var(), Var(), Var(), Var(), Var()
    ut = UnaryTape(tape, a, b)
    in_i_a = In(i, a)
    num_one = Num(one, 1)
    app = Apply(tape, i, one)

    exp = ut.expand()
    # exp = And(func, And(low, And(sep, And(high, beyond))))
    func_f = exp.left
    rest0 = exp.right  # And(low, And(sep, And(high, beyond)))
    low_f = rest0.left

    # Extract: ut -> rest0 -> low_f
    aer0 = and_elim_right(func_f, rest0, [])
    got_rest0 = apply_thm(aer0, [], ut, rest0, ax(ut))
    ael0 = and_elim_left(low_f, rest0.right, [])
    got_low = apply_thm(ael0, [], rest0, low_f, got_rest0)

    # Instantiate with i, then In(i,a), then one, then Num(one,1)
    got = apply_thm(got_low, [i], in_i_a,
        Forall(one, Implies(num_one, app)), ax(in_i_a))
    got = apply_thm(got, [one], num_one, app, ax(num_one))

    # Close
    for premise in [num_one, in_i_a, ut]:
        imp = Implies(premise, got.sequent.right[0])
        left = [f for f in got.sequent.left if not same(f, premise)]
        got = Proof(Sequent(left, [imp]), 'implies_right', [got], principal=imp)

    proof = got
    for v in [one, i, b, a, tape]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'tape_read_low'
    return proof


class Phase1Ind:
    """Strong induction predicate for Phase1 trace construction.
    Phase1Ind(n, d, q0, tape, c0) =
      ∃trace,cn. Function(trace) ∧ dom_bound(trace,n) ∧ base_cond(trace,c0) ∧
                 TMConfig(cn,q0,n,tape) ∧ Apply(trace,n,cn) ∧ step_valid(trace,n,d)"""
    __match_args__ = ('n', 'd', 'q0', 'tape', 'c0')
    def __init__(self, n, d, q0, tape, c0):
        self.n = n; self.d = d; self.q0 = q0; self.tape = tape; self.c0 = c0
    def expand(self):
        tra = Var(postfix='_tra'); cn = Var(postfix='_cn')
        k = Var(postfix='_k'); sk = Var(postfix='_sk')
        ck = Var(postfix='_ck'); ck1 = Var(postfix='_ck1')
        zp = Var(postfix='_zp')
        xd = Var(postfix='_xd'); yd = Var(postfix='_yd')
        base_cond = Forall(zp, Implies(Empty(zp), Apply(tra, zp, self.c0)))
        dom_bound = Forall(xd, Forall(yd, Implies(Apply(tra, xd, yd),
            Or(In(xd, self.n), Eq(xd, self.n)))))
        step_valid = Forall(k, Implies(In(k, self.n),
            Forall(sk, Implies(Successor(sk, k),
                Forall(ck, Implies(Apply(tra, k, ck),
                    Exists(ck1, And(Apply(tra, sk, ck1), TMStep(self.d, ck, ck1)))))))))
        return Exists(tra, Exists(cn, And(FuncDef(tra),
            And(dom_bound,
            And(base_cond,
            And(TMConfig(cn, self.q0, self.n, self.tape),
            And(Apply(tra, self.n, cn),
                step_valid)))))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Phase1Ind(r(self.n), r(self.d), r(self.q0), r(self.tape), r(self.c0))
    def __str__(self):
        return f'P1Ind({self.n},{self.d},{self.q0},{self.tape},{self.c0})'



def phase1_base():
    """Pairing |- ∀d,q0,z,tape,c0. Num(z,0) → TMConfig(c0,q0,z,tape) → Phase1Ind(z,d,q0,tape,c0)"""
    from core.proof import Proof, Sequent, same, _subst
    from tactics import apply_thm, mp, ax, eir, eel, cut, wl
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        or_intro_right, eq_reflexive, eq_symmetric, iff_mp_rev, unique_empty)
    from theorems.sets import ordpair_exists, singleton_exists
    from theorems.recursion import singleton_is_function, singleton_apply_eq, eq_apply_transfer
    from vocab.sets import Singleton

    def mk_and(gl, gr):
        L, R = gl.sequent.right[0], gr.sequent.right[0]
        return mp(apply_thm(and_intro(L, R, []), [], L, Implies(R, And(L, R)), gl), gr, R, And(L, R))

    d=Var(postfix='d');q0=Var(postfix='q0');z=Var(postfix='z')
    tape=Var(postfix='tape');c0=Var(postfix='c0')
    num_z=Num(z,0);cfg_c0=TMConfig(c0,q0,z,tape)
    goal = Phase1Ind(z, d, q0, tape, c0)

    # Build singleton trace {z→c0}
    pair_zc0=Var(postfix='pzc');t_sing=Var(postfix='ts')
    op_pair=OrdPair(pair_zc0,z,c0);sing_t=Singleton(t_sing,pair_zc0)
    oe=ordpair_exists();got_ex_pair=apply_thm(oe,[z,c0],concl=Exists(pair_zc0,op_pair))
    sif=singleton_is_function()
    got_func_s=apply_thm(sif,[pair_zc0,z,c0,t_sing])
    got_func_s=mp(got_func_s,ax(op_pair),op_pair,got_func_s.sequent.right[0].right)
    got_func_s=mp(got_func_s,ax(sing_t),sing_t,FuncDef(t_sing))

    # Apply(t_sing,z,c0)
    iff_is=Iff(In(pair_zc0,t_sing),Eq(pair_zc0,pair_zc0))
    got_iff_s=apply_thm(ax(sing_t),[pair_zc0],concl=iff_is)
    got_epp=apply_thm(eq_reflexive(),[pair_zc0])
    got_inp=mp(apply_thm(iff_mp_rev(In(pair_zc0,t_sing),Eq(pair_zc0,pair_zc0),[]),[],
        iff_is,Implies(Eq(pair_zc0,pair_zc0),In(pair_zc0,t_sing)),got_iff_s),
        got_epp,Eq(pair_zc0,pair_zc0),In(pair_zc0,t_sing))
    got_app_s=eir(mk_and(ax(op_pair),got_inp),And(op_pair,In(pair_zc0,t_sing)),pair_zc0,pair_zc0)

    # base_cond: ∀zp. Empty(zp) → Apply(t_sing,zp,c0)
    zp=Var(postfix='_zp')
    ue=unique_empty();es=eq_symmetric();eat=eq_apply_transfer()
    got_ezz=apply_thm(ue,[zp],Empty(zp),Forall(z,Implies(num_z,Eq(zp,z))),ax(Empty(zp)))
    got_ezz=apply_thm(got_ezz,[z],num_z,Eq(zp,z),ax(num_z))
    got_ezzp=apply_thm(es,[zp,z],Eq(zp,z),Eq(z,zp),got_ezz)
    got_azp=apply_thm(eat,[t_sing,z,zp,c0])
    got_azp=mp(got_azp,got_ezzp,Eq(z,zp),Implies(Apply(t_sing,z,c0),Apply(t_sing,zp,c0)))
    got_azp=mp(got_azp,got_app_s,Apply(t_sing,z,c0),Apply(t_sing,zp,c0))
    imp_b=Implies(Empty(zp),Apply(t_sing,zp,c0))
    lb=[f for f in got_azp.sequent.left if not same(f,Empty(zp))]
    got_bc=Proof(Sequent(lb,[imp_b]),'implies_right',[got_azp],principal=imp_b)
    got_bc=Proof(Sequent(got_bc.sequent.left,[Forall(zp,imp_b)]),'forall_right',[got_bc],principal=Forall(zp,imp_b),term=zp)

    # dom_bound: ∀xd,yd. Apply(t_sing,xd,yd) → Or(In(xd,z),Eq(xd,z))
    xd=Var(postfix='_xd');yd=Var(postfix='_yd')
    sae=singleton_apply_eq()
    got_sae=apply_thm(sae,[z,c0,pair_zc0,t_sing,xd,yd])
    got_sae=mp(got_sae,ax(op_pair),op_pair,got_sae.sequent.right[0].right)
    got_sae=mp(got_sae,ax(sing_t),sing_t,got_sae.sequent.right[0].right)
    got_sae=mp(got_sae,ax(Apply(t_sing,xd,yd)),Apply(t_sing,xd,yd),got_sae.sequent.right[0].right)
    got_ezxd=apply_thm(and_elim_left(Eq(z,xd),Eq(c0,yd),[]),[],got_sae.sequent.right[0],Eq(z,xd),got_sae)
    got_exdz=apply_thm(es,[z,xd],Eq(z,xd),Eq(xd,z),got_ezxd)
    or_xdz=Or(In(xd,z),Eq(xd,z))
    got_orx=apply_thm(or_intro_right(In(xd,z),Eq(xd,z),[]),[],Eq(xd,z),or_xdz,got_exdz)
    imp_db=Implies(Apply(t_sing,xd,yd),or_xdz)
    ldb=[f for f in got_orx.sequent.left if not same(f,Apply(t_sing,xd,yd))]
    got_db=Proof(Sequent(ldb,[imp_db]),'implies_right',[got_orx],principal=imp_db)
    got_db=Proof(Sequent(got_db.sequent.left,[Forall(yd,imp_db)]),'forall_right',[got_db],principal=Forall(yd,imp_db),term=yd)
    got_db=Proof(Sequent(got_db.sequent.left,[Forall(xd,Forall(yd,imp_db))]),'forall_right',[got_db],principal=Forall(xd,Forall(yd,imp_db)),term=xd)

    # step_valid: vacuous (∀k∈z=∅, impossible)
    _k=Var(postfix='_k');_sk=Var(postfix='_sk');_ck=Var(postfix='_ck');_ck1=Var(postfix='_ck1')
    got_nkz=apply_thm(ax(num_z),[_k])
    sv_inner=Forall(_sk,Implies(Successor(_sk,_k),Forall(_ck,Implies(Apply(t_sing,_k,_ck),Exists(_ck1,And(Apply(t_sing,_sk,_ck1),TMStep(d,_ck,_ck1)))))))
    nkz=Not(In(_k,z));gb=Proof(Sequent([In(_k,z),nkz],[]),'not_left',[ax(In(_k,z))],principal=nkz)
    gb=Proof(Sequent(gb.sequent.left,[sv_inner]),'weakening_right',[gb],principal=sv_inner)
    gb=cut(gb,nkz,got_nkz)
    imp_sv=Implies(In(_k,z),sv_inner);lsv=[f for f in gb.sequent.left if not same(f,In(_k,z))]
    got_sv=Proof(Sequent(lsv,[imp_sv]),'implies_right',[gb],principal=imp_sv)
    got_sv=Proof(Sequent(got_sv.sequent.left,[Forall(_k,imp_sv)]),'forall_right',[got_sv],principal=Forall(_k,imp_sv),term=_k)

    # Assemble Phase1Ind(z,...) via And + eir
    pza=mk_and(got_app_s,got_sv);pza=mk_and(ax(cfg_c0),pza)
    pza=mk_and(got_bc,pza);pza=mk_and(got_db,pza);pza=mk_and(got_func_s,pza)
    # eir: use goal.expand() structure
    exp = goal.expand()  # Exists(tra, Exists(cn, And(...)))
    tra_v = exp.var; inner_ex = exp.body  # Exists(cn, And(...))
    cn_v = inner_ex.var; and_body = inner_ex.body  # And(Function(tra), And(db, ...))
    # pza has the And with t_sing and c0. eir cn_v=c0, tra_v=t_sing.
    # Body for cn eir: and_body with tra_v=t_sing (cn_v free)
    from core.proof import _subst
    body_cn = _subst(and_body, tra_v, t_sing)  # And with t_sing, cn_v still free
    got_ecn = eir(pza, body_cn, cn_v, c0)
    # Body for trace eir: inner_ex with tra_v free
    got_etr = eir(got_ecn, inner_ex, tra_v, t_sing)
    assert same(got_etr.sequent.right[0], goal), f'Phase1Ind(z) mismatch'

    # eel singleton eigenvars
    se2=singleton_exists();got_es=apply_thm(se2,[pair_zc0],concl=Exists(t_sing,sing_t))
    got_etr=eel(got_etr,sing_t,t_sing);got_etr=cut(got_etr,Exists(t_sing,sing_t),got_es)
    got_etr=eel(got_etr,op_pair,pair_zc0);got_etr=cut(got_etr,Exists(pair_zc0,op_pair),got_ex_pair)

    # Discharge + ∀-close
    for hyp in [cfg_c0, num_z]:
        got_etr=wl(got_etr,hyp);imp=Implies(hyp,got_etr.sequent.right[0])
        left=[f for f in got_etr.sequent.left if not same(f,hyp)]
        got_etr=Proof(Sequent(left,[imp]),'implies_right',[got_etr],principal=imp)
    for v in [c0,tape,z,q0,d]:
        body=got_etr.sequent.right[0];fa=Forall(v,body)
        got_etr=Proof(Sequent(got_etr.sequent.left,[fa]),'forall_right',[got_etr],principal=fa,term=v)
    got_etr.name='phase1_base'
    return got_etr


def phase1_step_case():
    """ZFC |- ∀d,q0,a,b,tape,c0,n,sn,w,one.
        TMTransition(d,q0,one,one,one,q0) → Omega(w) → In(a,w) → In(n,w) →
        Function(d) → Function(tape) → Num(one,1) → UnaryTape(tape,a,b) →
        Successor(sn,n) → In(n,a) → Phase1Ind(n,d,q0,tape,c0) → Phase1Ind(sn,d,q0,tape,c0)"""
    from core.proof import Proof, Sequent, same, _subst
    from tactics import apply_thm, mp, ax, eir, eel, cut, wl
    from theorems.logic import and_intro, and_elim_left, and_elim_right
    from theorems.tm import tape_read_low, phase1_step_tmstep, phase1_step_extend_trace
    def mk_and(gl, gr):
        L, R = gl.sequent.right[0], gr.sequent.right[0]
        return mp(apply_thm(and_intro(L, R, []), [], L, Implies(R, And(L, R)), gl), gr, R, And(L, R))

    d=Var(postfix='d');q0=Var(postfix='q0');a=Var(postfix='a');b=Var(postfix='b')
    tape=Var(postfix='tape');c0=Var(postfix='c0')
    n=Var(postfix='n');sn=Var(postfix='sn');w=Var(postfix='w');one=Var(postfix='one')
    trans=TMTransition(d,q0,one,one,one,q0);omega_w=Omega(w);in_a_w=In(a,w)
    func_d=FuncDef(d);func_tape=FuncDef(tape);num_one=Num(one,1)
    utape=UnaryTape(tape,a,b);succ_sn=Successor(sn,n)
    pn=Phase1Ind(n,d,q0,tape,c0);psn=Phase1Ind(sn,d,q0,tape,c0)

    # Decompose Phase1Ind(n,...) by expanding
    pn_exp = pn.expand()  # Exists(tra, Exists(cn, And(...)))
    tra_v = pn_exp.var; pn_inner = pn_exp.body
    cn_v = pn_inner.var; pn_and = pn_inner.body
    # pn_and = And(Func(tra), And(db(tra,n), And(bc(tra), And(TMConfig(cn,q0,n,tape), And(Apply(tra,n,cn), sv(tra,n))))))
    b0=pn_and
    gft=apply_thm(and_elim_left(b0.left,b0.right,[]),[],b0,b0.left,ax(b0))
    b1=b0.right;gb1=apply_thm(and_elim_right(b0.left,b1,[]),[],b0,b1,ax(b0))
    gdb=apply_thm(and_elim_left(b1.left,b1.right,[]),[],b1,b1.left,gb1)
    b2=b1.right;gb2=apply_thm(and_elim_right(b1.left,b2,[]),[],b1,b2,gb1)
    gbt=apply_thm(and_elim_left(b2.left,b2.right,[]),[],b2,b2.left,gb2)
    b3=b2.right;gb3=apply_thm(and_elim_right(b2.left,b3,[]),[],b2,b3,gb2)
    gcn=apply_thm(and_elim_left(b3.left,b3.right,[]),[],b3,b3.left,gb3)
    b4=b3.right;gb4=apply_thm(and_elim_right(b3.left,b4,[]),[],b3,b4,gb3)
    gatn=apply_thm(and_elim_left(b4.left,b4.right,[]),[],b4,b4.left,gb4)
    gsvn=apply_thm(and_elim_right(b4.left,b4.right,[]),[],b4,b4.right,gb4)

    # tape_read_low: In(n,a) → Apply(tape,n,one)
    _trl=tape_read_low()
    gat=apply_thm(_trl,[tape,a,b,n,one])
    gat=mp(gat,ax(utape),utape,gat.sequent.right[0].right)
    gat=mp(gat,ax(In(n,a)),In(n,a),gat.sequent.right[0].right)
    gat=mp(gat,ax(num_one),num_one,Apply(tape,n,one))

    # phase1_step_tmstep: ∃cn_new. And(TMConfig(cn_new,q0,sn,tape), TMStep(d,cn,cn_new))
    _pst=phase1_step_tmstep()
    gts=apply_thm(_pst,[d,q0,n,sn,tape,cn_v,one,one])
    gts=mp(gts,ax(func_d),func_d,gts.sequent.right[0].right)
    gts=mp(gts,ax(trans),trans,gts.sequent.right[0].right)
    gts=mp(gts,gcn,gcn.sequent.right[0],gts.sequent.right[0].right)
    gts=mp(gts,ax(func_tape),func_tape,gts.sequent.right[0].right)
    gts=mp(gts,gat,Apply(tape,n,one),gts.sequent.right[0].right)
    gts=mp(gts,ax(num_one),num_one,gts.sequent.right[0].right)
    gts=mp(gts,ax(succ_sn),succ_sn,gts.sequent.right[0].right)

    # Open ∃cn_new
    tsx=gts.sequent.right[0];cnw=tsx.var;tsb=tsx.body
    gcfn=apply_thm(and_elim_left(tsb.left,tsb.right,[]),[],tsb,tsb.left,ax(tsb))
    gstn=apply_thm(and_elim_right(tsb.left,tsb.right,[]),[],tsb,tsb.right,ax(tsb))

    # phase1_step_extend_trace
    _pet=phase1_step_extend_trace()
    gext=apply_thm(_pet,[tra_v,sn,cnw,c0,n,d,cn_v,w])
    gext=mp(gext,gft,gft.sequent.right[0],gext.sequent.right[0].right)
    gext=mp(gext,gdb,gdb.sequent.right[0],gext.sequent.right[0].right)
    gext=mp(gext,ax(omega_w),omega_w,gext.sequent.right[0].right)
    gext=mp(gext,ax(In(n,w)),In(n,w),gext.sequent.right[0].right)
    gext=mp(gext,ax(succ_sn),succ_sn,gext.sequent.right[0].right)
    gext=mp(gext,gbt,gbt.sequent.right[0],gext.sequent.right[0].right)
    gext=mp(gext,gsvn,gsvn.sequent.right[0],gext.sequent.right[0].right)
    gext=mp(gext,gstn,gstn.sequent.right[0],gext.sequent.right[0].right)
    gext=mp(gext,gatn,gatn.sequent.right[0],gext.sequent.right[0].right)

    # Open ∃trn, decompose, insert TMConfig, reassemble Phase1Ind(sn,...)
    extx=gext.sequent.right[0];trn=extx.var;extb=extx.body
    e0=extb
    gef=apply_thm(and_elim_left(e0.left,e0.right,[]),[],e0,e0.left,ax(e0))
    e1=e0.right;ge1=apply_thm(and_elim_right(e0.left,e1,[]),[],e0,e1,ax(e0))
    gedb=apply_thm(and_elim_left(e1.left,e1.right,[]),[],e1,e1.left,ge1)
    e2=e1.right;ge2=apply_thm(and_elim_right(e1.left,e2,[]),[],e1,e2,ge1)
    gebc=apply_thm(and_elim_left(e2.left,e2.right,[]),[],e2,e2.left,ge2)
    e3=e2.right;ge3=apply_thm(and_elim_right(e2.left,e3,[]),[],e2,e3,ge2)
    geap=apply_thm(and_elim_left(e3.left,e3.right,[]),[],e3,e3.left,ge3)
    gesv=apply_thm(and_elim_right(e3.left,e3.right,[]),[],e3,e3.right,ge3)

    # Reassemble with TMConfig(cnw,q0,sn,tape) inserted
    psna=mk_and(geap,gesv);psna=mk_and(gcfn,psna);psna=mk_and(gebc,psna)
    psna=mk_and(gedb,psna);psna=mk_and(gef,psna)

    # eir using psn.expand() structure
    psn_exp=psn.expand();psn_tra=psn_exp.var;psn_inner=psn_exp.body
    psn_cn=psn_inner.var;psn_and=psn_inner.body
    from core.proof import _subst
    body_cn2=_subst(psn_and,psn_tra,trn)
    got_ecn2=eir(psna,body_cn2,psn_cn,cnw)
    got_etr2=eir(got_ecn2,psn_inner,psn_tra,trn)
    assert same(got_etr2.sequent.right[0],psn),f'Phase1Ind(sn) mismatch'

    # eel eigenvars
    got_etr2=eel(got_etr2,extb,trn);got_etr2=cut(got_etr2,extx,gext)
    got_etr2=eel(got_etr2,tsb,cnw);got_etr2=cut(got_etr2,tsx,gts)
    got_etr2=eel(got_etr2,pn_and,cn_v);got_etr2=cut(got_etr2,pn_inner,ax(pn_inner))
    got_etr2=eel(got_etr2,pn_inner,tra_v);got_etr2=cut(got_etr2,pn_exp,ax(pn))

    # Discharge + ∀-close
    hyps=[pn,In(n,a),succ_sn,num_one,utape,func_tape,func_d,In(n,w),in_a_w,omega_w,trans]
    for hyp in hyps:
        got_etr2=wl(got_etr2,hyp);imp=Implies(hyp,got_etr2.sequent.right[0])
        left=[f for f in got_etr2.sequent.left if not same(f,hyp)]
        got_etr2=Proof(Sequent(left,[imp]),'implies_right',[got_etr2],principal=imp)
    for v in [one,w,sn,n,c0,tape,b,a,q0,d]:
        body=got_etr2.sequent.right[0];fa=Forall(v,body)
        got_etr2=Proof(Sequent(got_etr2.sequent.left,[fa]),'forall_right',[got_etr2],principal=fa,term=v)
    got_etr2.name='phase1_step_case'
    return got_etr2


def phase1():
    """ZFC |- Phase1P()
    Omega induction using phase1_base + phase1_step_case, then extract TMReaches."""
    from core.proof import Proof, Sequent, same, _var_free_in_sequent, _subst
    from tactics import apply_thm, mp, ax, fl, eir, eel, cut, wl, wr, weaken_to
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        or_intro_left, or_intro_right, or_elim,
        eq_reflexive, eq_symmetric, iff_mp, iff_mp_rev, unique_empty, eq_substitution)
    from theorems.omega import omega_smallest_inductive, omega_contains_empty, omega_succ_closed
    from theorems.tm import Phase1P, tape_read_low, phase1_step_tmstep, phase1_step_extend_trace
    from theorems.sets import (ordpair_exists as _oe_fn, omega_transitive_set as ots_fn,
        eq_transfer, ordpair_unique as _ou_fn, singleton_exists)
    from vocab.sets import TransitiveSet
    from theorems.recursion import (singleton_is_function, singleton_apply_eq,
        eq_apply_transfer, eq_apply_val_transfer as _eavt_fn)
    import core.zfc as zfc

    def mk_and(gl, gr):
        L, R = gl.sequent.right[0], gr.sequent.right[0]
        return mp(apply_thm(and_intro(L, R, []), [], L, Implies(R, And(L, R)), gl), gr, R, And(L, R))

    d=Var(postfix='d');q0=Var(postfix='q0');z=Var(postfix='z')
    a=Var(postfix='a');tape=Var(postfix='tape');c0=Var(postfix='c0');c1=Var(postfix='c1')
    w=Var(postfix='w');one=Var(postfix='one');b=Var(postfix='b')
    n=Var(postfix='ind_n');sn=Var(postfix='ind_sn')
    pv=Var(postfix='ind_pv');xv=Var(postfix='ind_xv')
    trans=TMTransition(d,q0,one,one,one,q0);omega_w=Omega(w);in_a_w=In(a,w)
    func_d=FuncDef(d);func_tape=FuncDef(tape);num_one=Num(one,1);num_z=Num(z,0)
    utape=UnaryTape(tape,a,b);cfg_c0=TMConfig(c0,q0,z,tape);cfg_c1=TMConfig(c1,q0,a,tape)
    succ_sn=Successor(sn,n)
    pind_n = Phase1Ind(n,d,q0,tape,c0)

    def Q(nn): return Implies(Or(In(nn,a),Eq(nn,a)), Phase1Ind(nn,d,q0,tape,c0))

    # Separation
    # Q has free vars: a, d, q0, tape, c0 (plus nn which is the separation var)
    # Phase1Ind(nn,...).expand() introduces bound vars internally
    sep=zfc.Separation(Q,[a,d,q0,tape,c0])
    sep_ax=Proof(Sequent([sep],[sep]),'axiom',principal=sep)
    char_pv=Forall(xv,Iff(In(xv,pv),And(In(xv,w),Q(xv))))
    got_ex_pv=apply_thm(sep_ax,[c0,tape,q0,d,a,w],concl=Exists(pv,char_pv))

    def char_bwd(term,got_in_w,got_Q):
        gi=apply_thm(ax(char_pv),[term]);ii=gi.sequent.right[0];af=ii.right
        gr=apply_thm(iff_mp_rev(ii.left,ii.right,[]),[],ii,Implies(af,ii.left),gi)
        ai2=and_intro(af.left,af.right,[])
        ga=apply_thm(ai2,[],af.left,Implies(af.right,af),got_in_w)
        gand=mp(ga,got_Q,af.right,af);return mp(gr,gand,af,ii.left)

    def char_fwd(term):
        gi=apply_thm(ax(char_pv),[term]);ii=gi.sequent.right[0]
        gimp=apply_thm(iff_mp(ii.left,ii.right,[]),[],ii,Implies(ii.left,ii.right),gi)
        return mp(gimp,ax(In(term,pv)),In(term,pv),ii.right)

    print('phase1: sep done')

    # === BASE: In(z,pv) ===
    oce=omega_contains_empty()
    got_z_w=apply_thm(oce,[w],omega_w,Forall(z,Implies(num_z,In(z,w))),ax(omega_w))
    got_z_w=apply_thm(got_z_w,[z],num_z,In(z,w),ax(num_z))

    _pb=phase1_base()
    # _pb: Pairing |- ∀d,q0,z,tape,c0. Num(z,0)→TMConfig(c0,q0,z,tape)→Phase1Ind(z,d,q0,tape,c0)
    got_pb=apply_thm(_pb,[d,q0,z,tape,c0])
    got_pb=mp(got_pb,ax(num_z),num_z,got_pb.sequent.right[0].right)
    got_pb=mp(got_pb,ax(cfg_c0),cfg_c0,got_pb.sequent.right[0].right)
    # |- Phase1Ind(z,d,q0,tape,c0)

    # Q(z) = Or(In(z,a),Eq(z,a)) → Phase1Ind(z,...). Weaken with Or.
    or_za=Or(In(z,a),Eq(z,a))
    got_Qz=wl(got_pb,or_za)
    imp_qz=Implies(or_za,got_Qz.sequent.right[0])
    lqz=[f for f in got_Qz.sequent.left if not same(f,or_za)]
    got_Qz=Proof(Sequent(lqz,[imp_qz]),'implies_right',[got_Qz],principal=imp_qz)

    got_base_pv=char_bwd(z,got_z_w,got_Qz)

    # Inductive base: ∀zero_v. Empty(zero_v) → In(zero_v,pv)
    zero_v=Var(postfix='ind_zero')
    ue=unique_empty();es_thm=eq_substitution()
    got_eq=apply_thm(ue,[zero_v],Empty(zero_v),Forall(z,Implies(num_z,Eq(zero_v,z))),ax(Empty(zero_v)))
    got_eq=apply_thm(got_eq,[z],num_z,Eq(zero_v,z),ax(num_z))
    iff_zv=Iff(In(zero_v,pv),In(z,pv))
    got_iff=apply_thm(es_thm,[zero_v,z,pv],Eq(zero_v,z),iff_zv,got_eq)
    got_zv_pv=mp(apply_thm(iff_mp_rev(In(zero_v,pv),In(z,pv),[]),[],iff_zv,Implies(In(z,pv),In(zero_v,pv)),got_iff),
        got_base_pv,In(z,pv),In(zero_v,pv))
    imp_ez=Implies(Empty(zero_v),In(zero_v,pv))
    lez=[f for f in got_zv_pv.sequent.left if not same(f,Empty(zero_v))]
    got_ind_base=Proof(Sequent(lez,[imp_ez]),'implies_right',[got_zv_pv],principal=imp_ez)
    got_ind_base=Proof(Sequent(got_ind_base.sequent.left,[Forall(zero_v,imp_ez)]),
        'forall_right',[got_ind_base],principal=Forall(zero_v,imp_ez),term=zero_v)
    print('phase1: ind_base done')

    # === STEP: In(n,pv) → In(sn,pv) ===
    got_an=char_fwd(n)
    got_in_nw=apply_thm(and_elim_left(In(n,w),Q(n),[]),[],got_an.sequent.right[0],In(n,w),got_an)
    got_Qn=apply_thm(and_elim_right(In(n,w),Q(n),[]),[],got_an.sequent.right[0],Q(n),got_an)

    osc=omega_succ_closed()
    got_snw=apply_thm(osc,[w],omega_w,Forall(n,Implies(In(n,w),Forall(sn,Implies(succ_sn,In(sn,w))))),ax(omega_w))
    got_snw=apply_thm(got_snw,[n],In(n,w),Forall(sn,Implies(succ_sn,In(sn,w))),got_in_nw)
    got_snw=apply_thm(got_snw,[sn],succ_sn,In(sn,w),ax(succ_sn))

    # In(n,a) from Or(In(sn,a),Eq(sn,a)) via TransitiveSet(a)
    or_sna=Or(In(sn,a),Eq(sn,a))
    or_nsn=Or(In(n,n),Eq(n,n));iff_nsn=Iff(In(n,sn),or_nsn)
    got_insn=apply_thm(ax(succ_sn),[n],concl=iff_nsn)
    got_orn=apply_thm(or_intro_right(In(n,n),Eq(n,n),[]),[],Eq(n,n),or_nsn,apply_thm(eq_reflexive(),[n]))
    got_insn=mp(apply_thm(iff_mp_rev(In(n,sn),or_nsn,[]),[],iff_nsn,Implies(or_nsn,In(n,sn)),got_insn),got_orn,or_nsn,In(n,sn))
    _ots=ots_fn();gta=apply_thm(_ots,[w,a]);gta=mp(gta,ax(omega_w),omega_w,gta.sequent.right[0].right)
    gta=mp(gta,ax(in_a_w),in_a_w,TransitiveSet(a))
    gc1=apply_thm(gta,[sn]);cur=gc1.sequent.right[0];gc1=mp(gc1,ax(In(sn,a)),cur.left,cur.right)
    gc1=apply_thm(gc1,[n]);cur=gc1.sequent.right[0];gc1=mp(gc1,got_insn,cur.left,cur.right)
    _et=eq_transfer();gis=apply_thm(_et,[sn,a,n]);gis=mp(gis,ax(Eq(sn,a)),Eq(sn,a),gis.sequent.right[0].right)
    gc2=mp(apply_thm(iff_mp(In(n,sn),In(n,a),[]),[],Iff(In(n,sn),In(n,a)),Implies(In(n,sn),In(n,a)),gis),got_insn,In(n,sn),In(n,a))
    ic1=Implies(In(sn,a),In(n,a));lc1=[f for f in gc1.sequent.left if not same(f,In(sn,a))]
    gic1=Proof(Sequent(lc1,[ic1]),'implies_right',[gc1],principal=ic1)
    ic2=Implies(Eq(sn,a),In(n,a));lc2=[f for f in gc2.sequent.left if not same(f,Eq(sn,a))]
    gic2=Proof(Sequent(lc2,[ic2]),'implies_right',[gc2],principal=ic2)
    oena=or_elim(In(sn,a),Eq(sn,a),In(n,a),[])
    got_ina=apply_thm(oena,[],or_sna,Implies(ic1,Implies(ic2,In(n,a))),ax(or_sna))
    got_ina=mp(got_ina,gic1,ic1,Implies(ic2,In(n,a)));got_ina=mp(got_ina,gic2,ic2,In(n,a))

    # Q(n) → Phase1Ind(n,...) via Or(In(n,a),Eq(n,a))
    or_na=Or(In(n,a),Eq(n,a))
    got_orna=apply_thm(or_intro_left(In(n,a),Eq(n,a),[]),[],In(n,a),or_na,got_ina)
    got_Pn=mp(got_Qn,got_orna,or_na,pind_n)

    # phase1_step_case → Phase1Ind(sn,...) via instantiation + mp
    _psc=phase1_step_case()
    got_psc=apply_thm(_psc,[d,q0,a,b,tape,c0,n,sn,w,one])
    # Print implication chain to determine correct mp order
    from core.lang import Implies as _Imp
    _r=got_psc.sequent.right[0]; _i=0
    while type(_r) is _Imp:
        print(f'  step_case imp {_i}: {str(_r.left)[:60]}')
        _r=_r.right; _i+=1
    print(f'  step_case concl: {str(_r)[:60]}')
    got_psc=mp(got_psc,ax(trans),trans,got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,ax(omega_w),omega_w,got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,ax(in_a_w),in_a_w,got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,got_in_nw,In(n,w),got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,ax(func_d),func_d,got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,ax(func_tape),func_tape,got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,ax(utape),utape,got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,ax(num_one),num_one,got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,ax(succ_sn),succ_sn,got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,got_ina,In(n,a),got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,got_Pn,pind_n,got_psc.sequent.right[0].right)
    # |- Phase1Ind(sn,d,q0,tape,c0)

    # Q(sn) = Or(In(sn,a),Eq(sn,a)) → Phase1Ind(sn,...)
    pind_sn=Phase1Ind(sn,d,q0,tape,c0)
    imp_qsn=Implies(or_sna,pind_sn)
    lqsn=[f for f in got_psc.sequent.left if not same(f,or_sna)]
    got_Qsn=Proof(Sequent(lqsn,[imp_qsn]),'implies_right',[wl(got_psc,or_sna)],principal=imp_qsn)

    got_step_pv=char_bwd(sn,got_snw,got_Qsn)
    if any(same(In(n,w),f) for f in got_step_pv.sequent.left):
        got_step_pv=cut(got_step_pv,In(n,w),got_in_nw)
    print('phase1: step In(sn,pv) done')

    # Discharge sn, n
    proof=got_step_pv
    for ff in list(proof.sequent.left):
        if _var_free_in_sequent(sn,Sequent([ff],[])) and not same(ff,succ_sn):
            proof=wl(proof,ff);imp=Implies(ff,proof.sequent.right[0])
            left=[f for f in proof.sequent.left if not same(f,ff)]
            proof=Proof(Sequent(left,[imp]),'implies_right',[proof],principal=imp)
    imp_sn=Implies(succ_sn,proof.sequent.right[0])
    left_sn=[f for f in proof.sequent.left if not same(f,succ_sn)]
    proof=Proof(Sequent(left_sn,[imp_sn]),'implies_right',[proof],principal=imp_sn)
    proof=Proof(Sequent(proof.sequent.left,[Forall(sn,imp_sn)]),'forall_right',[proof],principal=Forall(sn,imp_sn),term=sn)
    for ff in list(proof.sequent.left):
        if _var_free_in_sequent(n,Sequent([ff],[])) and not same(ff,In(n,pv)):
            proof=wl(proof,ff);imp=Implies(ff,proof.sequent.right[0])
            left=[f for f in proof.sequent.left if not same(f,ff)]
            proof=Proof(Sequent(left,[imp]),'implies_right',[proof],principal=imp)
    imp_npv=Implies(In(n,pv),proof.sequent.right[0])
    left_npv=[f for f in proof.sequent.left if not same(f,In(n,pv))]
    got_ind_step=Proof(Sequent(left_npv,[imp_npv]),'implies_right',[proof],principal=imp_npv)
    got_ind_step=Proof(Sequent(got_ind_step.sequent.left,[Forall(n,imp_npv)]),'forall_right',[got_ind_step],principal=Forall(n,imp_npv),term=n)
    print('phase1: ind_step done')

    # === OSI ===
    all_ctx=list(got_ind_base.sequent.left)
    for f_ in got_ind_step.sequent.left:
        if not any(same(f_,g) for g in all_ctx): all_ctx.append(f_)
    gib_w=weaken_to(got_ind_base,all_ctx);gis_w=weaken_to(got_ind_step,all_ctx)
    ibf=gib_w.sequent.right[0];isf=gis_w.sequent.right[0];ai=And(ibf,isf)
    got_ind=mp(apply_thm(and_intro(ibf,isf,[]),[],ibf,Implies(isf,ai),gib_w),gis_w,isf,ai)

    xs2=Var(postfix='xs2');got_fwd=char_fwd(xs2)
    inxw=got_fwd.sequent.right[0].left
    got_xw=apply_thm(and_elim_left(inxw,got_fwd.sequent.right[0].right,[]),[],got_fwd.sequent.right[0],inxw,got_fwd)
    imp_sub=Implies(In(xs2,pv),inxw)
    ls=[f for f in got_xw.sequent.left if not same(f,In(xs2,pv))]
    got_sub=Proof(Sequent(ls,[imp_sub]),'implies_right',[got_xw],principal=imp_sub)
    spw=Forall(xs2,imp_sub)
    got_sub=Proof(Sequent(got_sub.sequent.left,[spw]),'forall_right',[got_sub],principal=spw,term=xs2)

    osi=omega_smallest_inductive();eq_pw=Eq(pv,w)
    got_osi=apply_thm(osi,[pv,w])
    while not same(got_osi.sequent.right[0],eq_pw):
        cur=got_osi.sequent.right[0];got_osi=mp(got_osi,ax(cur.left),cur.left,cur.right)
    all_osi=list(all_ctx)
    for f_ in got_sub.sequent.left:
        if not any(same(f_,g) for g in all_osi): all_osi.append(f_)
    gsw=weaken_to(got_sub,all_osi);giw=weaken_to(got_ind,all_osi)
    gas=mp(apply_thm(and_intro(spw,ai,[]),[],spw,Implies(ai,And(spw,ai)),gsw),giw,ai,And(spw,ai))
    for h in [f_ for f_ in got_osi.sequent.left if not isinstance(f_,zfc.ZFCAxiom) and not same(f_,omega_w)]:
        got_osi=cut(got_osi,h,gas)
    print('phase1: osi done')

    # === Extract Q(a) → Phase1Ind(a,...) ===
    iff_a=Iff(In(a,pv),In(a,w))
    got_iff_a=cut(fl(eq_pw,iff_a,a),eq_pw,got_osi)
    got_apv=mp(apply_thm(iff_mp_rev(In(a,pv),In(a,w),[]),[],iff_a,Implies(In(a,w),In(a,pv)),got_iff_a),ax(in_a_w),in_a_w,In(a,pv))
    got_anda=cut(char_fwd(a),In(a,pv),got_apv)
    got_Qa=apply_thm(and_elim_right(In(a,w),Q(a),[]),[],got_anda.sequent.right[0],Q(a),got_anda)
    or_aa=Or(In(a,a),Eq(a,a));got_oraa=apply_thm(or_intro_right(In(a,a),Eq(a,a),[]),[],Eq(a,a),or_aa,apply_thm(eq_reflexive(),[a]))
    pind_a=Phase1Ind(a,d,q0,tape,c0)
    got_Pa=mp(got_Qa,got_oraa,or_aa,pind_a)
    got_Pa=eel(got_Pa,char_pv,pv);got_Pa=cut(got_Pa,Exists(pv,char_pv),got_ex_pv)
    print('phase1: P(a) extracted')

    # === Phase1Ind(a,...) + TMConfig(c1,...) → TMReaches(d,c0,a,c1) ===
    # Put Phase1Ind(a,...) on left, open ∃tra,cn. Derive TMReaches(d,c0,a,c1).
    # cn is eigenvariable (not free on right since right has c1). tra also eigenvariable.
    pind_a=Phase1Ind(a,d,q0,tape,c0)
    pa_exp=pind_a.expand();pa_tra=pa_exp.var;pa_inner=pa_exp.body
    pa_cn=pa_inner.var;pa_and=pa_inner.body

    # Decompose pa_and from left
    b0=pa_and
    gft=apply_thm(and_elim_left(b0.left,b0.right,[]),[],b0,b0.left,ax(b0))
    b1=b0.right;gb1=apply_thm(and_elim_right(b0.left,b1,[]),[],b0,b1,ax(b0))
    b2=b1.right;gb2=apply_thm(and_elim_right(b1.left,b2,[]),[],b1,b2,gb1)
    gbt=apply_thm(and_elim_left(b2.left,b2.right,[]),[],b2,b2.left,gb2)
    b3=b2.right;gb3=apply_thm(and_elim_right(b2.left,b3,[]),[],b2,b3,gb2)
    gcna=apply_thm(and_elim_left(b3.left,b3.right,[]),[],b3,b3.left,gb3)
    b4=b3.right;gb4=apply_thm(and_elim_right(b3.left,b4,[]),[],b3,b4,gb3)
    gatna=apply_thm(and_elim_left(b4.left,b4.right,[]),[],b4,b4.left,gb4)
    gsva=apply_thm(and_elim_right(b4.left,b4.right,[]),[],b4,b4.right,gb4)
    # gcna: [pa_and] |- TMConfig(pa_cn,q0,a,tape)
    # gatna: [pa_and] |- Apply(pa_tra,a,pa_cn)
    # gbt: [pa_and] |- base_cond(pa_tra)
    # gsva: [pa_and] |- step_valid(pa_tra,a)

    # Eq(pa_cn,c1) from ordpair_unique on the config structure
    # TMConfig(cn,...) = ∀v. OrdPair(v,a,tape)→OrdPair(cn,q0,v)
    # TMConfig(c1,...) = ∀v. OrdPair(v,a,tape)→OrdPair(c1,q0,v)
    # Get a common inner pair via ordpair_exists, then ordpair_unique on outer.
    inner_v=Var(postfix='_iv');op_iv=OrdPair(inner_v,a,tape)
    got_ex_iv=apply_thm(_oe_fn(),[a,tape],concl=Exists(inner_v,op_iv))
    # TMConfig(pa_cn,...) inst with inner_v: OrdPair(inner_v,a,tape)→OrdPair(pa_cn,q0,inner_v)
    op_cn=OrdPair(pa_cn,q0,inner_v)
    got_op_cn=apply_thm(gcna,[inner_v],op_iv,op_cn,ax(op_iv))
    # TMConfig(c1,...) inst with inner_v:
    op_c1=OrdPair(c1,q0,inner_v)
    got_op_c1=apply_thm(ax(cfg_c1),[inner_v],op_iv,op_c1,ax(op_iv))
    # ordpair_unique: OrdPair(pa_cn,q0,inner_v)→OrdPair(c1,q0,inner_v)→Eq(pa_cn,c1)
    from theorems.sets import ordpair_unique as _ou_fn
    _ou=_ou_fn()
    got_eq=apply_thm(_ou,[q0,inner_v,pa_cn,c1])
    got_eq=mp(got_eq,got_op_cn,op_cn,got_eq.sequent.right[0].right)
    got_eq=mp(got_eq,got_op_c1,op_c1,Eq(pa_cn,c1))
    # eel inner_v
    got_eq=eel(got_eq,op_iv,inner_v);got_eq=cut(got_eq,Exists(inner_v,op_iv),got_ex_iv)
    # [...] |- Eq(pa_cn,c1)

    # Apply(pa_tra,a,c1) from Apply(pa_tra,a,pa_cn) + Eq(pa_cn,c1)
    from theorems.recursion import eq_apply_val_transfer as _eavt_fn
    _eavt=_eavt_fn()
    got_at_c1=apply_thm(_eavt,[pa_tra,a,pa_cn,c1])
    got_at_c1=mp(got_at_c1,got_eq,Eq(pa_cn,c1),got_at_c1.sequent.right[0].right)
    got_at_c1=mp(got_at_c1,gatna,gatna.sequent.right[0],Apply(pa_tra,a,c1))

    # Build TMReaches(d,c0,a,c1) = ∃trace. And(base, And(step, Apply(trace,a,c1)))
    reaches=TMReaches(d,c0,a,c1)
    rexp=reaches.expand();r_tra=rexp.var;r_body=rexp.body
    r_and=mk_and(gsva,got_at_c1);r_and=mk_and(gbt,r_and)
    got_reaches=eir(r_and,r_body,r_tra,pa_tra)
    got_reaches=cut(ax(reaches),reaches,got_reaches)
    # [pa_and, TMConfig(c1,...), Pairing] |- TMReaches(d,c0,a,c1)
    # c1 is free on right. pa_cn is NOT free on right (only cn appears via pa_and on left).
    # pa_tra NOT free on right (eir bound it).
    # eel pa_cn from pa_and: pa_cn free in pa_and (left) but NOT on right. ✓
    got_reaches=eel(got_reaches,pa_and,pa_cn)
    # [Exists(pa_cn,pa_and)=pa_inner, TMConfig(c1,...), Pairing] |- TMReaches(d,c0,a,c1)
    # eel pa_tra from pa_inner: pa_tra free in pa_inner (left) but NOT on right. ✓
    got_reaches=eel(got_reaches,pa_inner,pa_tra)
    # [Exists(pa_tra,pa_inner)=pind_a, TMConfig(c1,...), Pairing] |- TMReaches(d,c0,a,c1)
    got_reaches=cut(got_reaches,pind_a,got_Pa)
    # [TMConfig(c1,...), Pairing, ...ZFC from got_Pa...] |- TMReaches(d,c0,a,c1)
    print(f'phase1: TMReaches(d,c0,a,c1) derived')

    # === Discharge + forall-close → Phase1P ===
    goal_hyps=[trans,omega_w,in_a_w,func_d,func_tape,num_one,num_z,utape,cfg_c0,cfg_c1]
    for hyp in reversed(goal_hyps):
        got_reaches=wl(got_reaches,hyp);imp=Implies(hyp,got_reaches.sequent.right[0])
        left=[f for f in got_reaches.sequent.left if not same(f,hyp)]
        got_reaches=Proof(Sequent(left,[imp]),'implies_right',[got_reaches],principal=imp)
    for v in [c1,c0,b,one,w,tape,a,z,q0,d]:
        body=got_reaches.sequent.right[0];fa=Forall(v,body)
        got_reaches=Proof(Sequent(got_reaches.sequent.left,[fa]),'forall_right',[got_reaches],principal=fa,term=v)

    # Wrap as Phase1P vocab object
    goal=Phase1P()
    got_reaches=cut(ax(goal),goal,got_reaches)
    assert same(got_reaches.sequent.right[0],goal,expand=False), \
        f'Phase1P mismatch'
    print('phase1: VERIFIED — proves Phase1P')
    got_reaches.name='phase1'
    return got_reaches



