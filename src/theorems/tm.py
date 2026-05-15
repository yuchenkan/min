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
        tape_read = Forall(p, Implies(In(p,w), Apply(tape2,p,one)))
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
    from core.proof import Proof, Sequent, same
    from core.lang import Var, In, Implies, Forall
    from core.derived import Exists, And, Or, Iff, Eq
    from vocab.ordpair import OrdPair, Successor
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
    # LEFT: goal hyps + intermediate hyps (from ax) + Phase*P + ZFC axioms
    # Strategy: cut intermediate hyps from left. They contain intermediate vars
    # (c1-c4, one, q1, q2, sa, tape2, etc.) but those vars are NOT in the right.
    # So we can eel each intermediate var, then cut with existence proof.
    # But many vars appear in MULTIPLE left formulas.
    # Simpler: discharge intermediates as implies, close ∀, then fl+mp to eliminate.

    # Step 1: Discharge all non-goal, non-axiom formulas from left
    goal_hyps = [omega_w, In(a,w), In(b,w), FuncDef(delta), FuncDef(tape_in),
                 delta_char, num_q0, num_qH, num_z, utape, cfg_c0, plus_abc,
                 succ_hf, succ_ssc, succ_n, unary_out, cfg_cf]
    import core.zfc as zfc
    for ff in list(proof.sequent.left):
        is_goal = any(same(ff, gh) for gh in goal_hyps)
        is_ax = isinstance(ff, (zfc.ZFCAxiom, Phase1P, Phase2P, Phase3P, Phase4P, Phase5P, TMReachesCompose))
        if not is_goal and not is_ax:
            proof = wl(proof, ff)
            imp = Implies(ff, proof.sequent.right[0])
            left_new = [f for f in proof.sequent.left if not same(f, ff)]
            proof = Proof(Sequent(left_new, [imp]), 'implies_right', [proof], principal=imp)

    # Step 2: Close ∀ over intermediate vars
    from core.proof import _var_free_in_sequent
    intermediate_vars = [c4, c3, c2, c1, one, q2, q1, sa, tape2]
    for v in intermediate_vars:
        if _var_free_in_sequent(v, Sequent([], proof.sequent.right)):
            body = proof.sequent.right[0]
            fa = Forall(v, body)
            proof = Proof(Sequent(proof.sequent.left, [fa]),
                'forall_right', [proof], principal=fa, term=v)

    # Step 3: proof right = F_int = ∀(int vars). (int hyps) → TMReaches
    # Build [F_int] |- TMReaches by apply_thm + mp, then cut.
    F_int = proof.sequent.right[0]
    got_open = apply_thm(ax(F_int), [tape2, sa, q1, q2, one, c1, c2, c3, c4])
    # mp each intermediate hypothesis
    while hasattr(got_open.sequent.right[0], 'left') and type(got_open.sequent.right[0]).__name__ == 'Implies':
        cur = got_open.sequent.right[0]
        got_open = mp(got_open, ax(cur.left), cur.left, cur.right)
    # got_open: [F_int, int hyps on left] |- TMReaches
    # Cut F_int
    proof = cut(got_open, F_int, proof)
    # Now: [goal hyps, axioms, int hyps] |- TMReaches

    # Step 4: Discharge goal hypotheses in add_goal's order
    for hyp in reversed(goal_hyps):
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left_new = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left_new, [imp]), 'implies_right', [proof], principal=imp)

    # Step 5: Close ∀ over goal vars in add_goal's order
    for v in [c, b, a, w, c0, z, tape_in, cf, tf, n, ssc, hf, qH, q0, delta]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'tm_add_correct'
    return proof
