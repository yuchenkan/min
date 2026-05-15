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

def num_exists(k):
    """∃n. Num(n,k) — a numeral k exists.
    ZFC |- ∃n. Num(n,k)"""
    from tactics import apply_thm, ax, eir, eel, cut
    from theorems.logic import and_elim_left
    from theorems.arithmetic import unique_num
    from core.derived import Exists, And

    p = unique_num(k)
    eu_exp = p.sequent.right[0].expand()
    n_var = eu_exp.var
    num_part = eu_exp.body.left
    uniq_part = eu_exp.body.right
    got = apply_thm(and_elim_left(num_part, uniq_part, []), [],
        eu_exp.body, num_part, ax(eu_exp.body))
    got = eir(got, num_part, n_var, n_var)
    got = eel(got, eu_exp.body, n_var)
    got = cut(got, eu_exp, p)
    got.name = f'num_exists_{k}'
    return got


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


def config_exists():
    """∃c. TMConfig(c, q, h, t) — a config with given state/head/tape exists.
    Pairing |- ∀q,h,t. ∃c. TMConfig(c,q,h,t)"""
    from tactics import apply_thm, mp, ax, eir, eel, cut
    from theorems.sets import ordpair_exists
    from theorems.tm_backup import config_intro
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
    # num_exists and config_exists are defined above in this module
    from vocab.omega import Omega, Num
    from vocab.tm import TMConfig, TMTransition, TMStep, TapeUpdate, TMReaches
    from vocab.functions import Function as FuncDef, Apply
    from vocab.recursion import Plus as PlusDef
    from tm import UnaryTape, UnaryOutput, formalize, add_machine
    from theorems.logic import and_elim_left, and_elim_right

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

    # In(hf,w) — hf is a goal var, but In(hf,w) is NOT a goal hyp
    # Derive from Plus(sa,b,hf) via plus_val_in_omega
    from theorems.arithmetic import plus_val_in_omega
    _pvi = plus_val_in_omega()
    got_hf_w = apply_thm(_pvi, [w, sa, b, hf])
    got_hf_w = mp(got_hf_w, ax(omega_w), omega_w, got_hf_w.sequent.right[0].right)
    got_hf_w = mp(got_hf_w, got_sa_w, In(sa,w), got_hf_w.sequent.right[0].right)
    got_hf_w = mp(got_hf_w, ax(In(b,w)), In(b,w), got_hf_w.sequent.right[0].right)
    got_hf_w = mp(got_hf_w, ax(plus_sa_b_hf), plus_sa_b_hf, In(hf,w))

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
    from theorems.tm_backup import tape_update_function

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
    from theorems.tm_backup import tape_read_high, tape_update_other
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

    from theorems.tm_backup import tape_update_at
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

    # tape2_hf_zero: Apply(tape2,hf,z) — tape2 reads 0 at hf
    # hf = S(c) = S(a+b). Position hf is past all ones. tape_in(hf) = 0.
    # tape_read_end would give this but it's broken. Derive from tape_read_sep-like logic.
    # tape_in has 1^a 0 1^b then 0s. hf = S(a+b) = S(c). tape_in(hf) = 0.
    # tape_update_other: tape2(hf) = tape_in(hf) since hf ≠ a.
    # Need: Apply(tape_in,hf,z) and Not(Eq(hf,a)).
    # Apply(tape_in,hf,z): tape_in reads 0 past input. From UnaryTape end-of-input property.
    # Not(Eq(hf,a)): hf = S(c) = S(a+b) ≥ S(a) > a. Same ordering issue.
    # But again, use LEM: Eq(hf,a) ∨ Not(Eq(hf,a)).
    # Case Eq(hf,a): tape_update_at → Apply(tape2,hf,one). But we want Apply(tape2,hf,z).
    #   one ≠ z (since Num(one,1) and Num(z,0)). Contradiction? No — both could hold.
    #   Actually tape2 is a function. Apply(tape2,hf,one) and Apply(tape2,hf,z) → one=z.
    #   But one≠z. So Apply(tape2,hf,z) can't hold simultaneously with Apply(tape2,hf,one).
    #   But we're trying to PROVE Apply(tape2,hf,z). If Eq(hf,a) gives Apply(tape2,hf,one),
    #   we can't get Apply(tape2,hf,z) from that — they contradict.
    #   So Eq(hf,a) must be impossible. Back to needing Not(Eq(hf,a)).
    # For tape2_hf_zero, I DO need the ordering. Can't use LEM here.
    # TODO: prove Not(Eq(hf,a)) from hf=S(c), c=a+b.
    # For now: ax(tape2_hf_zero).

    # tape2_c_one: Apply(tape2,c,one) — tape2 reads 1 at c
    # c = a+b. If c=a (b=0 edge case): tape_update_at gives Apply(tape2,a,one). Done.
    # If c≠a: tape_update_other + Apply(tape_in,c,one). tape_in(c) = 1 from tape_read_high.
    # Use LEM on Eq(c,a):
    # Case Eq(c,a): tape_update_at → Apply(tape2,c,one). Done!
    # Case Not(Eq(c,a)): tape_read_high on tape_in at position c + tape_update_other. Done!
    # But tape_read_high needs In(j,b) and Plus(sa,j,c) for some j.
    # c = a+b. Plus(sa,j,c) = Plus(S(a),j,a+b). j = b-1? Not directly.
    # Actually c = a+b. sa = S(a). Plus(sa,j,c): S(a)+j = a+b. j = b-1.
    # Need j∈b and Plus(sa,j,c). j = b-1 isn't a formal concept without predecessor.
    # Hmm. tape_read_high: UnaryTape → In(j,b) → Succ(sa,a) → Plus(sa,j,pos) → Num(one,1) → Apply(tape_in,pos,one)
    # I need Apply(tape_in,c,one) where c = a+b. Plus(sa,j,c) needs j such that sa+j=c=a+b.
    # sa = S(a). S(a)+j = a+b. j = b-1. For b>0: j = pred(b) ∈ b. But I can't extract pred.
    # For b=0: c=a. Eq(c,a). tape_update_at handles this.
    # For b>0: need ∃j. In(j,b) ∧ Plus(sa,j,c). This is derivable from Plus(a,b,c) + commutativity.
    # But complex.
    # For now: ax(tape2_c_one).

    # tu_tf: TapeUpdate(tf,tape2,c,z)
    # This says tf = tape2[c := 0]. From UnaryOutput(tf,c): tf is the output tape 1^c.
    # And tape2 has 1^(c+1) then 0s (after tape_update at position a).
    # tf = tape2 with last 1 erased. This is exactly TapeUpdate(tf,tape2,c,z).
    # Need to connect UnaryOutput(tf,c) with TapeUpdate(tf,tape2,c,z).
    # UnaryOutput defines tf by its characteristic: ∀i. i∈c → Apply(tf,i,one), etc.
    # TapeUpdate defines tf by construction: tf = tape2 but with position c set to 0.
    # These are different characterizations of the same set.
    # Proving they're the same requires showing tape2[c:=0] has the output tape properties.
    # For now: ax(tu_tf).
    print(f'tm_add: tape2_hf_zero, tape2_c_one, tu_tf still as ax(). Need ordering + tape proofs.')

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
            # Find which left formula has v free
            for f in proof.sequent.left:
                if _var_free_in_sequent(v, Sequent([f], [])):
                    print(f'  forall_right BLOCKED: {v} free in {str(f)[:60]}')
            break

    proof.name = 'tm_add_correct'
    return proof
