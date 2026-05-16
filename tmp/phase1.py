"""Phase1P proof: omega induction building trace for scanning past a ones.

Target: Phase1P() from ZFC only.
∀d,q0,z,a,tape,c0,c1,w,one,b.
  TMTransition(d,q0,one,one,one,q0) → Omega(w) → In(a,w) → Function(d) → Function(tape) →
  Num(one,1) → Num(z,0) → UnaryTape(tape,a,b) →
  TMConfig(c0,q0,z,tape) → TMConfig(c1,q0,a,tape) → TMReaches(d,c0,a,c1)

Approach: omega induction on a with Q(n) = (In(n,a)∨Eq(n,a)) → P(n).
P(n) = ∃trace,cn. Function(trace) ∧ base(trace) ∧ TMConfig(cn,q0,n,tape) ∧
        Apply(trace,n,cn) ∧ step_valid(trace,n)
"""
import sys; sys.path.insert(0, '/root/min/src')

from core.lang import Var, In, Not, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq
from core.proof import Proof, Sequent, same, _var_free_in_sequent
from vocab.ordpair import OrdPair, Successor
from vocab.omega import Omega, Num
from vocab.sets import Empty
from vocab.tm import TMConfig, TMTransition, TMStep, TapeUpdate, HeadMove, TMReaches
from vocab.functions import Function as FuncDef, Apply
from vocab.recursion import Plus as PlusDef
from tm import UnaryTape, UnaryOutput
from tactics import apply_thm, mp, ax, fl, eir, eel, cut, wl, wr, weaken_to
from theorems.logic import (and_intro, and_elim_left, and_elim_right,
    or_intro_left, or_intro_right, or_elim,
    eq_reflexive, eq_symmetric, eq_transitive,
    iff_mp, iff_mp_rev, iff_chain, unique_empty, eq_substitution)
from theorems.sets import (successor_exists, eq_transfer, omega_no_self_membership,
    ordpair_exists, ordpair_unique)
from theorems.omega import (omega_smallest_inductive, omega_contains_empty,
    omega_succ_closed, func_unique_thm)
from theorems.tm import (tape_read_low, phase1_step_tmstep, phase1_step_extend_trace,
    config_exists, config_intro, config_decompose)
from theorems.arithmetic import num_exists
from theorems.recursion import eq_apply_val_transfer
import core.zfc as zfc


def phase1():
    # Variables matching Phase1P
    d = Var(postfix='d'); q0 = Var(postfix='q0'); z = Var(postfix='z')
    a = Var(postfix='a'); tape = Var(postfix='tape')
    c0 = Var(postfix='c0'); c1 = Var(postfix='c1')
    w = Var(postfix='w'); one = Var(postfix='one'); b = Var(postfix='b')

    # Hypotheses
    trans = TMTransition(d, q0, one, one, one, q0)
    omega_w = Omega(w)
    in_a_w = In(a, w)
    func_d = FuncDef(d)
    func_tape = FuncDef(tape)
    num_one = Num(one, 1)
    num_z = Num(z, 0)
    utape = UnaryTape(tape, a, b)
    cfg_c0 = TMConfig(c0, q0, z, tape)
    cfg_c1 = TMConfig(c1, q0, a, tape)

    # Induction variables
    n = Var(postfix='ind_n'); sn = Var(postfix='ind_sn')
    pv = Var(postfix='ind_pv'); xv = Var(postfix='ind_xv')

    # P(n) components
    trace = Var(postfix='tra'); cn = Var(postfix='cn')
    k = Var(postfix='k'); sk = Var(postfix='sk')
    ck = Var(postfix='ck'); ck1 = Var(postfix='ck1')
    z_prime = Var(postfix='zp')

    def base_cond(tr):
        return Forall(z_prime, Implies(Empty(z_prime), Apply(tr, z_prime, c0)))

    def step_valid(tr, nn):
        return Forall(k, Implies(In(k, nn),
            Forall(sk, Implies(Successor(sk, k),
                Forall(ck, Implies(Apply(tr, k, ck),
                    Exists(ck1, And(Apply(tr, sk, ck1), TMStep(d, ck, ck1)))))))))

    def P(nn):
        """The strong induction predicate."""
        return Exists(trace, Exists(cn, And(FuncDef(trace),
            And(base_cond(trace),
            And(TMConfig(cn, q0, nn, tape),
            And(Apply(trace, nn, cn),
                step_valid(trace, nn)))))))

    def Q(nn):
        """Guarded predicate for omega induction."""
        return Implies(Or(In(nn, a), Eq(nn, a)), P(nn))

    # === Separation for omega induction ===
    sep = zfc.Separation(Q, [a, d, q0, z, tape, c0, w, one, b,
                             trace, cn, k, sk, ck, ck1, z_prime])
    sep_ax = Proof(Sequent([sep], [sep]), 'axiom', principal=sep)
    char_pv = Forall(xv, Iff(In(xv, pv), And(In(xv, w), Q(xv))))
    got_ex_pv = apply_thm(sep_ax, [z_prime, ck1, ck, sk, k, cn, trace,
                                    b, one, w, c0, tape, z, q0, d, a, w],
                           concl=Exists(pv, char_pv))
    print('phase1: Separation done')

    def char_bwd(term, got_in_w, got_Q):
        got_inst = apply_thm(ax(char_pv), [term])
        iff_inst = got_inst.sequent.right[0]
        and_form = iff_inst.right
        got_rev = apply_thm(iff_mp_rev(iff_inst.left, iff_inst.right, []),
            [], iff_inst, Implies(and_form, iff_inst.left), got_inst)
        ai = and_intro(and_form.left, and_form.right, [])
        got_ai = apply_thm(ai, [], and_form.left, Implies(and_form.right, and_form), got_in_w)
        got_and = mp(got_ai, got_Q, and_form.right, and_form)
        return mp(got_rev, got_and, and_form, iff_inst.left)

    def char_fwd(term):
        got_inst = apply_thm(ax(char_pv), [term])
        iff_inst = got_inst.sequent.right[0]
        got_imp = apply_thm(iff_mp(iff_inst.left, iff_inst.right, []),
            [], iff_inst, Implies(iff_inst.left, iff_inst.right), got_inst)
        return mp(got_imp, ax(In(term, pv)), In(term, pv), iff_inst.right)

    def mk_and(got_l, got_r):
        L, R = got_l.sequent.right[0], got_r.sequent.right[0]
        return mp(apply_thm(and_intro(L, R, []), [], L, Implies(R, And(L, R)), got_l),
            got_r, R, And(L, R))

    # === Base case: Q(z) ===
    # Q(z) = (In(z,a)∨Eq(z,a)) → P(z)
    # P(z) needs trace with trace(0)=c0, TMConfig(c0,q0,z,tape), step_valid vacuous (∀k∈z=∅, vacuous).
    # Use singleton function {z→c0} as trace.
    # For now just prove Q(z) is vacuously achievable with a singleton trace.

    # First, derive In(z,w)
    oce = omega_contains_empty()
    got_z_w = apply_thm(oce, [w], omega_w, Forall(z, Implies(num_z, In(z, w))), ax(omega_w))
    got_z_w = apply_thm(got_z_w, [z], num_z, In(z, w), ax(num_z))

    # Build P(z): need trace singleton, Function, base, TMConfig(c0,q0,z,tape), Apply(trace,z,c0), step_valid
    # Singleton trace: from recursion.py singleton_is_function + singleton_apply_eq
    from theorems.recursion import singleton_is_function

    # singleton_is_function: ∀a,b,f. Singleton(f,⟨a,b⟩) → Function(f)
    # singleton_apply_eq: ∀f,a,b. Singleton(f,⟨a,b⟩) → OrdPair(p,a,b) → Apply(f,a,b)
    # Actually let me check what these give us exactly.

    # We need a trace t with Apply(t,z,c0). Construct via ordpair_exists:
    # ∃pair. OrdPair(pair,z,c0). Then Singleton(t,pair). Function(t). Apply(t,z,c0).

    pair_zc0 = Var(postfix='pair_zc0')
    t_sing = Var(postfix='t_sing')
    op_pair = OrdPair(pair_zc0, z, c0)
    from vocab.sets import Singleton
    sing_t = Singleton(t_sing, pair_zc0)

    oe = ordpair_exists()
    got_ex_pair = apply_thm(oe, [z, c0], concl=Exists(pair_zc0, op_pair))

    # singleton_is_function: Singleton(f,p) → OrdPair(p,a,b) → Function(f)
    sif = singleton_is_function()
    # sif: ∀sp,sx,sy,sv. OrdPair(sp,sx,sy) → Singleton(sv,sp) → Function(sv)
    got_func_sing = apply_thm(sif, [pair_zc0, z, c0, t_sing])
    got_func_sing = mp(got_func_sing, ax(op_pair), op_pair, got_func_sing.sequent.right[0].right)
    got_func_sing = mp(got_func_sing, ax(sing_t), sing_t, FuncDef(t_sing))
    # [Singleton(t_sing,pair_zc0), OrdPair(pair_zc0,z,c0), Pairing] |- Function(t_sing)

    # Derive Apply(t_sing,z,c0) = ∃p. OrdPair(p,z,c0) ∧ In(p,t_sing)
    # From Singleton(t_sing,pair_zc0): ∀x. x∈t_sing ↔ x=pair_zc0
    # At x=pair_zc0: In(pair_zc0,t_sing) ← Eq(pair_zc0,pair_zc0) via Iff reverse.
    iff_in_sing = Iff(In(pair_zc0, t_sing), Eq(pair_zc0, pair_zc0))
    got_iff_sing = apply_thm(ax(sing_t), [pair_zc0], concl=iff_in_sing)
    er = eq_reflexive()
    got_eq_pp = apply_thm(er, [pair_zc0])
    got_in_p_t = mp(apply_thm(iff_mp_rev(In(pair_zc0, t_sing), Eq(pair_zc0, pair_zc0), []),
        [], iff_in_sing, Implies(Eq(pair_zc0, pair_zc0), In(pair_zc0, t_sing)), got_iff_sing),
        got_eq_pp, Eq(pair_zc0, pair_zc0), In(pair_zc0, t_sing))
    # [Singleton(t_sing,pair_zc0)] |- In(pair_zc0, t_sing)
    # Build And(OrdPair(pair_zc0,z,c0), In(pair_zc0,t_sing)) → eir → Apply(t_sing,z,c0)
    got_and_app = mk_and(ax(op_pair), got_in_p_t)
    got_app_sing = eir(got_and_app, And(OrdPair(pair_zc0, z, c0), In(pair_zc0, t_sing)), pair_zc0, pair_zc0)
    # [OrdPair(pair_zc0,z,c0), Singleton(t_sing,pair_zc0)] |- Apply(t_sing,z,c0)

    # base_cond(t_sing): ∀z'. Empty(z') → Apply(t_sing,z',c0)
    # From Apply(t_sing,z,c0) and Empty(z'): Eq(z',z) via unique_empty+Num(z,0).
    # Then eq_apply_transfer: Apply(t_sing,z,c0) → Apply(t_sing,z',c0).
    # Actually eq_apply_transfer transfers first arg: Eq(z,z')→Apply(t,z,c0)→Apply(t,z',c0).
    # Need Eq(z,z'). From Empty(z')→Num(z,0)→Eq(z',z) via unique_empty. Then eq_symmetric→Eq(z,z').
    from theorems.recursion import eq_apply_transfer as eat_fn
    ue = unique_empty()
    es = eq_symmetric()
    eat = eat_fn()

    zp = z_prime
    got_eq_zpz = apply_thm(ue, [zp], Empty(zp), Forall(z, Implies(num_z, Eq(zp, z))), ax(Empty(zp)))
    got_eq_zpz = apply_thm(got_eq_zpz, [z], num_z, Eq(zp, z), ax(num_z))
    got_eq_zzp = apply_thm(es, [zp, z], Eq(zp, z), Eq(z, zp), got_eq_zpz)
    got_app_zp = apply_thm(eat, [t_sing, z, zp, c0])
    got_app_zp = mp(got_app_zp, got_eq_zzp, Eq(z, zp), Implies(Apply(t_sing, z, c0), Apply(t_sing, zp, c0)))
    got_app_zp = mp(got_app_zp, got_app_sing, Apply(t_sing, z, c0), Apply(t_sing, zp, c0))
    # [Empty(zp), Num(z,0), Singleton, OrdPair, Pairing] |- Apply(t_sing,zp,c0)

    # Discharge Empty(zp), close ∀zp: base_cond(t_sing)
    imp_base = Implies(Empty(zp), Apply(t_sing, zp, c0))
    left_base = [f for f in got_app_zp.sequent.left if not same(f, Empty(zp))]
    got_base_cond = Proof(Sequent(left_base, [imp_base]), 'implies_right', [got_app_zp], principal=imp_base)
    fa_base = Forall(zp, imp_base)
    got_base_cond = Proof(Sequent(got_base_cond.sequent.left, [fa_base]),
        'forall_right', [got_base_cond], principal=fa_base, term=zp)
    # |- base_cond(t_sing) = ∀z'.Empty(z')→Apply(t_sing,z',c0)

    # step_valid(t_sing, z): ∀k∈z. ... — vacuously true since z=∅ has no elements
    # ∀k. In(k,z) → ... is vacuous when z=∅ (Empty(z) means ¬∃x.In(x,z))
    # Prove it by: assume In(k,z). From Num(z,0)=Empty(z): ¬In(k,z). Contradiction → anything.
    sv_body_inner = Forall(sk, Implies(Successor(sk, k),
        Forall(ck, Implies(Apply(t_sing, k, ck),
            Exists(ck1, And(Apply(t_sing, sk, ck1), TMStep(d, ck, ck1)))))))
    # From [In(k,z), Num(z,0)] derive contradiction → sv_body_inner
    # Num(z,0) = Empty(z) = ∀x.¬In(x,z). Instantiate with k: ¬In(k,z).
    not_in_kz = Not(In(k, z))
    # Num(z,0) = Empty(z) = ∀x.¬In(x,z). Instantiate with k: ¬In(k,z).
    got_not_kz = apply_thm(ax(num_z), [k])
    # [Num(z,0)] |- Not(In(k,z))
    got_bot = Proof(Sequent([In(k, z), not_in_kz], []), 'not_left', [ax(In(k, z))], principal=not_in_kz)
    got_bot = Proof(Sequent(got_bot.sequent.left, [sv_body_inner]), 'weakening_right', [got_bot], principal=sv_body_inner)
    got_bot = cut(got_bot, not_in_kz, got_not_kz)
    # [In(k,z), Num(z,0)] |- sv_body_inner
    imp_sv = Implies(In(k, z), sv_body_inner)
    left_sv = [f for f in got_bot.sequent.left if not same(f, In(k, z))]
    got_sv = Proof(Sequent(left_sv, [imp_sv]), 'implies_right', [got_bot], principal=imp_sv)
    fa_sv = Forall(k, imp_sv)
    got_sv = Proof(Sequent(got_sv.sequent.left, [fa_sv]), 'forall_right', [got_sv], principal=fa_sv, term=k)
    # [Num(z,0)] |- step_valid(t_sing, z)
    print('phase1: base step_valid done')

    # Assemble P(z):
    # And(Function(t_sing), And(base_cond, And(TMConfig(c0,q0,z,tape), And(Apply(t_sing,z,c0), step_valid))))
    got_cfg_c0 = ax(cfg_c0)  # TMConfig(c0,q0,z,tape) — from hypothesis

    p_z_and = mk_and(got_app_sing, got_sv)  # And(Apply(t_sing,z,c0), step_valid)
    p_z_and = mk_and(got_cfg_c0, p_z_and)   # And(TMConfig, And(Apply, step_valid))
    p_z_and = mk_and(got_base_cond, p_z_and) # And(base_cond, And(TMConfig, And(Apply, step_valid)))
    p_z_and = mk_and(got_func_sing, p_z_and) # And(Function, And(base_cond, And(TMConfig, And(Apply, step_valid))))

    # eir cn=c0, trace=t_sing
    p_z_body = P(z).body  # Exists(cn, And(Function,...))
    # Actually P(z) = Exists(trace, Exists(cn, ...))
    # Need to eir trace=t_sing, cn=c0
    got_P_z = eir(p_z_and, p_z_and.sequent.right[0], cn, c0)  # ∃cn. ...
    # Hmm, need to match P(z)'s structure. Let me check P(z):
    pz = P(z)
    print(f'P(z) = {str(pz)[:100]}')
    print(f'p_z_and right = {str(p_z_and.sequent.right[0])[:100]}')

    # The eir should introduce ∃cn with witness c0, then ∃trace with witness t_sing.
    # But eir needs the body to match the And structure exactly.
    # P(z) = Exists(trace, Exists(cn, And(FuncDef(trace), And(base_cond(trace), And(TMConfig(cn,q0,z,tape), And(Apply(trace,z,cn), step_valid(trace,z)))))))
    # My got has: And(FuncDef(t_sing), And(base_cond(t_sing), And(TMConfig(c0,q0,z,tape), And(Apply(t_sing,z,c0), step_valid(t_sing,z)))))
    # To get ∃cn: substitute cn for c0 in the body pattern, witness=c0
    # To get ∃trace: substitute trace for t_sing in the body pattern, witness=t_sing

    # This is the tricky part. The Exists vars in P(z) are 'trace' and 'cn' (specific Var objects).
    # eir(proof, body_with_witness, var, witness) converts body_with_witness to ∃var.body_with_var.
    # So: eir(got, And_with_c0_and_t_sing, cn, c0) → ∃cn. And_with_cn_and_t_sing
    # Then: eir(result, ∃cn.And_with_cn_and_t_sing, trace, t_sing) → ∃trace.∃cn.And_with_cn_and_trace

    # But eir substitutes witness→var in the body. So if my body has c0 where cn should be,
    # eir(got, body, cn, c0) creates Exists(cn, body[c0→cn]).
    # And if body also has t_sing where trace should be, the second eir would need body to have t_sing.

    # Let me just try it and see what happens.
    # First eir cn (witness c0): converts Apply(t_sing,z,c0) to Apply(t_sing,z,cn), TMConfig(c0,...) to TMConfig(cn,...)
    inner_and = p_z_and.sequent.right[0]  # And(FuncDef(t_sing), And(base_cond(t_sing), And(TMConfig(c0,...), And(Apply(t_sing,z,c0), sv(t_sing,z)))))
    # eir order: first cn (inner), then trace (outer).
    # body_for_cn = BODY with t_sing for trace, cn free:
    body_for_cn = And(FuncDef(t_sing),
        And(base_cond(t_sing),
        And(TMConfig(cn, q0, z, tape),
        And(Apply(t_sing, z, cn),
            step_valid(t_sing, z)))))
    # proof has body_for_cn[cn:=c0] on right (p_z_and)
    got_ex_cn = eir(p_z_and, body_for_cn, cn, c0)
    print(f'After eir cn: {str(got_ex_cn.sequent.right[0])[:80]}')

    # body_for_trace = Exists(cn, BODY) with trace free = P(z).body
    pz_inner = P(z)
    body_for_trace = pz_inner.body  # Exists(cn, BODY_with_trace_and_cn)
    got_ex_tr = eir(got_ex_cn, body_for_trace, trace, t_sing)
    print(f'After eir trace: {str(got_ex_tr.sequent.right[0])[:80]}')
    print(f'same(result, P(z))? {same(got_ex_tr.sequent.right[0], pz)}')

    # Eliminate singleton construction eigenvars
    from theorems.sets import singleton_exists
    se = singleton_exists()
    got_ex_sing = apply_thm(se, [pair_zc0], concl=Exists(t_sing, sing_t))
    got_ex_tr = eel(got_ex_tr, sing_t, t_sing)
    got_ex_tr = cut(got_ex_tr, Exists(t_sing, sing_t), got_ex_sing)
    got_ex_tr = eel(got_ex_tr, op_pair, pair_zc0)
    got_ex_tr = cut(got_ex_tr, Exists(pair_zc0, op_pair), got_ex_pair)
    print(f'P(z) proved. Left: {len(got_ex_tr.sequent.left)}')
    for f in got_ex_tr.sequent.left:
        print(f'  {str(f)[:60]}')

    # Now Q(z) = (In(z,a)∨Eq(z,a)) → P(z). Since P(z) is proved unconditionally (from hypotheses),
    # Q(z) follows by weakening.
    or_za = Or(In(z, a), Eq(z, a))
    got_Q_z = wl(got_ex_tr, or_za)
    imp_qz = Implies(or_za, got_Q_z.sequent.right[0])
    left_qz = [f for f in got_Q_z.sequent.left if not same(f, or_za)]
    got_Q_z = Proof(Sequent(left_qz, [imp_qz]), 'implies_right', [got_Q_z], principal=imp_qz)
    print(f'Q(z) done. same(Q(z), target)? {same(got_Q_z.sequent.right[0], Q(z))}')


if __name__ == '__main__':
    phase1()
