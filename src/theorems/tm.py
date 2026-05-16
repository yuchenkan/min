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
      Num(one,1) → Num(zero,0) →
      Successor(sa,a) → TapeUpdate(tape2,tape,a,one) →
      TMConfig(c1,q0,a,tape) → TMConfig(c2,q1,sa,tape2) →
      TMReaches(d,c1,one,c2)"""
    def expand(self):
        d,q0,q1,a,sa,one = Var(postfix='_d'), Var(postfix='_q0'), Var(postfix='_q1'), Var(postfix='_a'), Var(postfix='_sa'), Var(postfix='_one')
        tape,tape2 = Var(postfix='_tape'), Var(postfix='_t2')
        c1,c2 = Var(postfix='_c1'), Var(postfix='_c2')
        zero = Var(postfix='_z')
        body = Implies(TMTransition(d,q0,zero,one,one,q1),
            Implies(FuncDef(d), Implies(FuncDef(tape),
            Implies(Num(one,1), Implies(Num(zero,0),
            Implies(Successor(sa,a), Implies(TapeUpdate(tape2,tape,a,one),
            Implies(TMConfig(c1,q0,a,tape), Implies(TMConfig(c2,q1,sa,tape2),
            TMReaches(d,c1,one,c2))))))))))
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

    # === Helper: mp through hypothesis list, using derived proofs where available ===
    derived_proofs = [trans_q0_1, trans_q0_0, trans_q1_1, trans_q1_0, trans_q2_1]
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
         num_one, num_zero, succ_sa, tu_tape2, cfg_c1, cfg_c2])

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



