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
    ∀d,q0,z,a,tape,c0,c1,w,one,d1,b.
      TMTransition(d,q0,one,one,d1,q0) →
      Omega(w) → In(a,w) → Function(d) → Function(tape) →
      Num(one,1) → Num(d1,1) → Num(z,0) → UnaryTape(tape,a,b) →
      TMConfig(c0,q0,z,tape) → TMConfig(c1,q0,a,tape) →
      TMReaches(d,c0,a,c1)"""
    def expand(self):
        d,q0,z,a,tape = Var(postfix='_d'), Var(postfix='_q0'), Var(postfix='_z'), Var(postfix='_a'), Var(postfix='_tape')
        c0,c1 = Var(postfix='_c0'), Var(postfix='_c1')
        w,one,d1,b = Var(postfix='_w'), Var(postfix='_one'), Var(postfix='_d1'), Var(postfix='_b')
        body = Implies(TMTransition(d,q0,one,one,d1,q0),
            Implies(Omega(w), Implies(In(a,w), Implies(FuncDef(d), Implies(FuncDef(tape),
            Implies(Num(one,1), Implies(Num(d1,1), Implies(Num(z,0), Implies(UnaryTape(tape,a,b),
            Implies(TMConfig(c0,q0,z,tape), Implies(TMConfig(c1,q0,a,tape),
            TMReaches(d,c0,a,c1))))))))))))
        for v in [c1,c0,b,d1,one,w,tape,a,z,q0,d]:
            body = Forall(v, body)
        return body
    def __str__(self): return 'Phase1P'


class Phase2P:
    """Phase 2: write 1 over separator, move R, change state. 1 step.
    ∀d,q0,q1,a,sa,one,d1,zero,tape,tape2,c1,c2.
      TMTransition(d,q0,zero,one,d1,q1) →
      Function(d) → Function(tape) →
      Num(one,1) → Num(d1,1) → Num(zero,0) →
      Successor(sa,a) → TapeUpdate(tape2,tape,a,one) →
      TMConfig(c1,q0,a,tape) → TMConfig(c2,q1,sa,tape2) →
      TMReaches(d,c1,one,c2)"""
    def expand(self):
        d,q0,q1,a,sa,one,d1 = Var(postfix='_d'), Var(postfix='_q0'), Var(postfix='_q1'), Var(postfix='_a'), Var(postfix='_sa'), Var(postfix='_one'), Var(postfix='_d1')
        tape,tape2 = Var(postfix='_tape'), Var(postfix='_t2')
        c1,c2 = Var(postfix='_c1'), Var(postfix='_c2')
        zero = Var(postfix='_z')
        body = Implies(TMTransition(d,q0,zero,one,d1,q1),
            Implies(FuncDef(d), Implies(FuncDef(tape),
            Implies(Num(one,1), Implies(Num(d1,1), Implies(Num(zero,0),
            Implies(Successor(sa,a), Implies(TapeUpdate(tape2,tape,a,one),
            Implies(TMConfig(c1,q0,a,tape), Implies(TMConfig(c2,q1,sa,tape2),
            TMReaches(d,c1,one,c2)))))))))))
        for v in [c2,c1,tape2,tape,zero,d1,one,sa,a,q1,q0,d]:
            body = Forall(v, body)
        return body
    def __str__(self): return 'Phase2P'


class Phase3P:
    """Phase 3: scan right past b ones. b steps.
    ∀d,q1,sa,b,pos,tape2,c1,c2,w,one,d1.
      TMTransition(d,q1,one,one,d1,q1) →
      Omega(w) → In(b,w) → In(sa,w) →
      Function(d) → Function(tape2) →
      Num(one,1) → Num(d1,1) →
      (∀p. In(p,w) → Apply(tape2,p,one)) →
      Plus(sa,b,pos) →
      TMConfig(c1,q1,sa,tape2) → TMConfig(c2,q1,pos,tape2) →
      TMReaches(d,c1,b,c2)"""
    def expand(self):
        d,q1,sa,b,pos = Var(postfix='_d'), Var(postfix='_q1'), Var(postfix='_sa'), Var(postfix='_b'), Var(postfix='_pos')
        tape2 = Var(postfix='_t2')
        c1,c2 = Var(postfix='_c1'), Var(postfix='_c2')
        w,one,d1 = Var(postfix='_w'), Var(postfix='_one'), Var(postfix='_d1')
        p = Var(postfix='_p')
        tape_read = Forall(p, Implies(In(p,w), Apply(tape2,p,one)))
        body = Implies(TMTransition(d,q1,one,one,d1,q1),
            Implies(Omega(w), Implies(In(b,w), Implies(In(sa,w),
            Implies(FuncDef(d), Implies(FuncDef(tape2),
            Implies(Num(one,1), Implies(Num(d1,1), Implies(tape_read,
            Implies(PlusDef(sa,b,pos),
            Implies(TMConfig(c1,q1,sa,tape2), Implies(TMConfig(c2,q1,pos,tape2),
            TMReaches(d,c1,b,c2)))))))))))))
        for v in [c2,c1,d1,one,w,tape2,pos,b,sa,q1,d]:
            body = Forall(v, body)
        return body
    def __str__(self): return 'Phase3P'


class Phase4P:
    """Phase 4: read 0 past ones, write 0, move L. 1 step.
    ∀d,q1,q2,hf,c,one,d1,zero,tape2,c1,c2.
      TMTransition(d,q1,zero,zero,d1,q2) →
      Function(d) → Function(tape2) →
      Num(one,1) → Num(d1,1) → Num(zero,0) →
      Successor(hf,c) → Apply(tape2,hf,zero) →
      TMConfig(c1,q1,hf,tape2) → TMConfig(c2,q2,c,tape2) →
      TMReaches(d,c1,one,c2)"""
    def expand(self):
        d,q1,q2,hf,c,one,d1 = Var(postfix='_d'), Var(postfix='_q1'), Var(postfix='_q2'), Var(postfix='_hf'), Var(postfix='_c'), Var(postfix='_one'), Var(postfix='_d1')
        zero = Var(postfix='_z')
        tape2 = Var(postfix='_t2')
        c1,c2 = Var(postfix='_c1'), Var(postfix='_c2')
        body = Implies(TMTransition(d,q1,zero,zero,d1,q2),
            Implies(FuncDef(d), Implies(FuncDef(tape2),
            Implies(Num(one,1), Implies(Num(d1,1), Implies(Num(zero,0),
            Implies(Successor(hf,c), Implies(Apply(tape2,hf,zero),
            Implies(TMConfig(c1,q1,hf,tape2), Implies(TMConfig(c2,q2,c,tape2),
            TMReaches(d,c1,one,c2)))))))))))
        for v in [c2,c1,tape2,zero,d1,one,c,hf,q2,q1,d]:
            body = Forall(v, body)
        return body
    def __str__(self): return 'Phase4P'


class Phase5P:
    """Phase 5: erase last 1, move R, halt. 1 step.
    ∀d,q2,qH,c,hf,one,d1,zero,tape2,tf,c1,c2.
      TMTransition(d,q2,one,zero,d1,qH) →
      Function(d) → Function(tape2) →
      Num(one,1) → Num(d1,1) → Num(zero,0) →
      Successor(hf,c) → Apply(tape2,c,one) →
      TapeUpdate(tf,tape2,c,zero) →
      TMConfig(c1,q2,c,tape2) → TMConfig(c2,qH,hf,tf) →
      TMReaches(d,c1,one,c2)"""
    def expand(self):
        d,q2,qH,c,hf,one,d1 = Var(postfix='_d'), Var(postfix='_q2'), Var(postfix='_qH'), Var(postfix='_c'), Var(postfix='_hf'), Var(postfix='_one'), Var(postfix='_d1')
        zero = Var(postfix='_z')
        tape2,tf = Var(postfix='_t2'), Var(postfix='_tf')
        c1,c2 = Var(postfix='_c1'), Var(postfix='_c2')
        body = Implies(TMTransition(d,q2,one,zero,d1,qH),
            Implies(FuncDef(d), Implies(FuncDef(tape2),
            Implies(Num(one,1), Implies(Num(d1,1), Implies(Num(zero,0),
            Implies(Successor(hf,c), Implies(Apply(tape2,c,one),
            Implies(TapeUpdate(tf,tape2,c,zero),
            Implies(TMConfig(c1,q2,c,tape2), Implies(TMConfig(c2,qH,hf,tf),
            TMReaches(d,c1,one,c2))))))))))))
        for v in [c2,c1,tf,tape2,zero,d1,one,hf,c,qH,q2,d]:
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
# tm_add_correct: chain Phase1P..Phase5P via TMReachesCompose
# ============================================================

def tm_add_correct():
    """TM addition correctness: the unary addition machine halts with correct output.
    [Phase1P, Phase2P, Phase3P, Phase4P, Phase5P, TMReachesCompose, ZFC axioms]
    |- forall delta,q0,qH,tape_in,z,c0,w,a,b,c,hf,ssc,n,tf,cf,
            q1,q2,sa,one,d1,zero,tape2,
            c1,c2,c3,c4.
         ... hypotheses ... →
         TMReaches(delta,c0,n,cf)
    """
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from core.proof import Proof, Sequent, same

    # Variables
    delta = Var(postfix='delta')
    q0,q1,q2,qH = Var(postfix='q0'), Var(postfix='q1'), Var(postfix='q2'), Var(postfix='qH')
    z = Var(postfix='z')
    tape_in = Var(postfix='tin')
    tape2 = Var(postfix='t2')
    tf = Var(postfix='tf')
    c0 = Var(postfix='c0')
    cf = Var(postfix='cf')
    a,b,c = Var(postfix='a'), Var(postfix='b'), Var(postfix='c')
    sa = Var(postfix='sa')
    hf = Var(postfix='hf')
    ssc = Var(postfix='ssc')
    n = Var(postfix='n')
    w = Var(postfix='w')
    one = Var(postfix='one')
    d1 = Var(postfix='d1')
    zero = Var(postfix='zv')
    c1,c2,c3,c4 = Var(postfix='c1'), Var(postfix='c2'), Var(postfix='c3'), Var(postfix='c4')

    # Hypotheses
    omega_w = Omega(w)
    num_z = Num(z, 0)
    num_zero = Num(zero, 0)
    num_one = Num(one, 1)
    num_d1 = Num(d1, 1)
    succ_sa = Successor(sa, a)
    succ_hf = Successor(hf, c)
    succ_ssc = Successor(ssc, hf)
    succ_n = Successor(n, ssc)
    plus_abc = PlusDef(a, b, c)
    tu_tape2 = TapeUpdate(tape2, tape_in, a, one)
    tu_tf = TapeUpdate(tf, tape2, c, zero)
    utape = UnaryTape(tape_in, a, b)

    cfg_c0 = TMConfig(c0, q0, z, tape_in)
    cfg_c1 = TMConfig(c1, q0, a, tape_in)
    cfg_c2 = TMConfig(c2, q1, sa, tape2)
    cfg_c3 = TMConfig(c3, q1, hf, tape2)
    cfg_c4 = TMConfig(c4, q2, c, tape2)
    cfg_cf = TMConfig(cf, qH, hf, tf)

    trans_q0_1 = TMTransition(delta, q0, one, one, d1, q0)
    trans_q0_0 = TMTransition(delta, q0, zero, one, d1, q1)
    trans_q1_1 = TMTransition(delta, q1, one, one, d1, q1)
    trans_q1_0 = TMTransition(delta, q1, zero, zero, d1, q2)
    trans_q2_1 = TMTransition(delta, q2, one, zero, d1, qH)

    tp = Var(postfix='tp')
    tape_read = Forall(tp, Implies(In(tp, w), Apply(tape2, tp, one)))
    tape2_hf_zero = Apply(tape2, hf, zero)
    tape2_c_one = Apply(tape2, c, one)
    plus_sa_b_hf = PlusDef(sa, b, hf)

    # === Instantiate Phase1P → TMReaches(delta, c0, a, c1) ===
    # ∀ order: d,q0,z,a,tape,w,one,d1,b,c0,c1
    got_p1 = apply_thm(ax(Phase1P()), [delta, q0, z, a, tape_in, w, one, d1, b, c0, c1])
    for h in [trans_q0_1, omega_w, In(a,w), FuncDef(delta), FuncDef(tape_in),
              num_one, num_d1, num_z, utape, cfg_c0, cfg_c1]:
        got_p1 = mp(got_p1, ax(h), h, got_p1.sequent.right[0].right)

    # === Instantiate Phase2P → TMReaches(delta, c1, one, c2) ===
    # ∀ order: d,q0,q1,a,sa,one,d1,zero,tape,tape2,c1,c2
    got_p2 = apply_thm(ax(Phase2P()), [delta, q0, q1, a, sa, one, d1, zero, tape_in, tape2, c1, c2])
    for h in [trans_q0_0, FuncDef(delta), FuncDef(tape_in),
              num_one, num_d1, num_zero, succ_sa, tu_tape2, cfg_c1, cfg_c2]:
        got_p2 = mp(got_p2, ax(h), h, got_p2.sequent.right[0].right)

    # === Instantiate Phase3P → TMReaches(delta, c2, b, c3) ===
    # ∀ order: d,q1,sa,b,pos,tape2,w,one,d1,c1,c2
    got_p3 = apply_thm(ax(Phase3P()), [delta, q1, sa, b, hf, tape2, w, one, d1, c2, c3])
    for h in [trans_q1_1, omega_w, In(b,w), In(sa,w),
              FuncDef(delta), FuncDef(tape2),
              num_one, num_d1, tape_read,
              plus_sa_b_hf, cfg_c2, cfg_c3]:
        got_p3 = mp(got_p3, ax(h), h, got_p3.sequent.right[0].right)

    # === Instantiate Phase4P → TMReaches(delta, c3, one, c4) ===
    # ∀ order: d,q1,q2,hf,c,one,d1,zero,tape2,c1,c2
    got_p4 = apply_thm(ax(Phase4P()), [delta, q1, q2, hf, c, one, d1, zero, tape2, c3, c4])
    for h in [trans_q1_0, FuncDef(delta), FuncDef(tape2),
              num_one, num_d1, num_zero, succ_hf, tape2_hf_zero, cfg_c3, cfg_c4]:
        got_p4 = mp(got_p4, ax(h), h, got_p4.sequent.right[0].right)

    # === Instantiate Phase5P → TMReaches(delta, c4, one, cf) ===
    # ∀ order: d,q2,qH,c,hf,one,d1,zero,tape2,tf,c1,c2
    got_p5 = apply_thm(ax(Phase5P()), [delta, q2, qH, c, hf, one, d1, zero, tape2, tf, c4, cf])
    for h in [trans_q2_1, FuncDef(delta), FuncDef(tape2),
              num_one, num_d1, num_zero, succ_hf, tape2_c_one, tu_tf, cfg_c4, cfg_cf]:
        got_p5 = mp(got_p5, ax(h), h, got_p5.sequent.right[0].right)
    # got_p5: [Phase5P, hyps] |- TMReaches(delta, c4, one, cf)

    # === Compose: chain 5 TMReaches into TMReaches(delta, c0, n, cf) ===
    comp = TMReachesCompose()

    # Plus facts needed:
    # Plus(a, one, sa) — from plus_succ: Plus(a,0,a) + Succ(one,0) + Succ(sa,a)
    # Plus(sa, b, hf) — hypothesis plus_sa_b_hf
    # Plus(hf, one, ssc) — from Succ(ssc,hf) similarly
    # Plus(ssc, one, n) — from Succ(n,ssc) similarly
    plus_a_one_sa = PlusDef(a, one, sa)
    plus_hf_one_ssc = PlusDef(hf, one, ssc)
    plus_ssc_one_n = PlusDef(ssc, one, n)

    # Chain 1: TMReaches(d,c0,a,c1) + TMReaches(d,c1,one,c2) + Plus(a,one,sa) → TMReaches(d,c0,sa,c2)
    got_12 = apply_thm(ax(comp), [delta, c0, c1, c2, a, one, sa, w])
    got_12 = mp(got_12, got_p1, got_p1.sequent.right[0], got_12.sequent.right[0].right)
    got_12 = mp(got_12, got_p2, got_p2.sequent.right[0], got_12.sequent.right[0].right)
    got_12 = mp(got_12, ax(plus_a_one_sa), plus_a_one_sa, got_12.sequent.right[0].right)
    got_12 = mp(got_12, ax(omega_w), omega_w, got_12.sequent.right[0].right)
    got_12 = mp(got_12, ax(In(a,w)), In(a,w), got_12.sequent.right[0].right)
    got_12 = mp(got_12, ax(In(one,w)), In(one,w), got_12.sequent.right[0].right)
    # got_12: |- TMReaches(delta, c0, sa, c2)

    # Chain 2: TMReaches(d,c0,sa,c2) + TMReaches(d,c2,b,c3) + Plus(sa,b,hf) → TMReaches(d,c0,hf,c3)
    got_123 = apply_thm(ax(comp), [delta, c0, c2, c3, sa, b, hf, w])
    got_123 = mp(got_123, got_12, got_12.sequent.right[0], got_123.sequent.right[0].right)
    got_123 = mp(got_123, got_p3, got_p3.sequent.right[0], got_123.sequent.right[0].right)
    got_123 = mp(got_123, ax(plus_sa_b_hf), plus_sa_b_hf, got_123.sequent.right[0].right)
    got_123 = mp(got_123, ax(omega_w), omega_w, got_123.sequent.right[0].right)
    got_123 = mp(got_123, ax(In(sa,w)), In(sa,w), got_123.sequent.right[0].right)
    got_123 = mp(got_123, ax(In(b,w)), In(b,w), got_123.sequent.right[0].right)
    # got_123: |- TMReaches(delta, c0, hf, c3)

    # Chain 3: + Phase4 + Plus(hf,one,ssc) → TMReaches(d,c0,ssc,c4)
    got_1234 = apply_thm(ax(comp), [delta, c0, c3, c4, hf, one, ssc, w])
    got_1234 = mp(got_1234, got_123, got_123.sequent.right[0], got_1234.sequent.right[0].right)
    got_1234 = mp(got_1234, got_p4, got_p4.sequent.right[0], got_1234.sequent.right[0].right)
    got_1234 = mp(got_1234, ax(plus_hf_one_ssc), plus_hf_one_ssc, got_1234.sequent.right[0].right)
    got_1234 = mp(got_1234, ax(omega_w), omega_w, got_1234.sequent.right[0].right)
    got_1234 = mp(got_1234, ax(In(hf,w)), In(hf,w), got_1234.sequent.right[0].right)
    got_1234 = mp(got_1234, ax(In(one,w)), In(one,w), got_1234.sequent.right[0].right)
    # got_1234: |- TMReaches(delta, c0, ssc, c4)

    # Chain 4: + Phase5 + Plus(ssc,one,n) → TMReaches(d,c0,n,cf)
    got_all = apply_thm(ax(comp), [delta, c0, c4, cf, ssc, one, n, w])
    got_all = mp(got_all, got_1234, got_1234.sequent.right[0], got_all.sequent.right[0].right)
    got_all = mp(got_all, got_p5, got_p5.sequent.right[0], got_all.sequent.right[0].right)
    got_all = mp(got_all, ax(plus_ssc_one_n), plus_ssc_one_n, got_all.sequent.right[0].right)
    got_all = mp(got_all, ax(omega_w), omega_w, got_all.sequent.right[0].right)
    got_all = mp(got_all, ax(In(ssc,w)), In(ssc,w), got_all.sequent.right[0].right)
    got_all = mp(got_all, ax(In(one,w)), In(one,w), got_all.sequent.right[0].right)
    # got_all: |- TMReaches(delta, c0, n, cf)

    # Discharge all hypotheses as implications, close ∀
    proof = got_all
    hyps = [cfg_cf, UnaryOutput(tf,c), succ_n, succ_ssc, succ_hf, plus_abc,
            cfg_c0, utape, num_z, Num(qH,1), Num(q0,0),
            # delta_char transitions
            trans_q2_1, trans_q1_0, trans_q1_1, trans_q0_0, trans_q0_1,
            FuncDef(tape_in), FuncDef(delta),
            In(b,w), In(a,w), omega_w,
            # derived/intermediate hypotheses
            plus_ssc_one_n, plus_hf_one_ssc, plus_a_one_sa, plus_sa_b_hf,
            In(ssc,w), In(hf,w), In(sa,w), In(one,w),
            FuncDef(tape2), tape_read, tape2_hf_zero, tape2_c_one,
            tu_tape2, tu_tf,
            num_one, num_d1, num_zero, succ_sa,
            cfg_c1, cfg_c2, cfg_c3, cfg_c4,
            Num(q1,2), Num(q2,3)]
    for hyp in hyps:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [c4,c3,c2,c1,zero,d1,one,q2,q1,sa,tape2,
              tf,n,ssc,hf,c,b,a,cf,c0,w,z,tape_in,qH,q0,delta]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    proof.name = 'tm_add_correct'
    return proof
