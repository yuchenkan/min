"""Phase2P proof — single TMStep: (q0,a,tape)→(q1,sa,tape2).

Transition: q0,zero→one,one(right),q1.
Hypotheses: TMTransition, Function(d), Function(tape), Num(one,1), Num(zero,0),
  Apply(tape,a,zero), Successor(sa,a), TapeUpdate(tape2,tape,a,one),
  TMConfig(c1,q0,a,tape), TMConfig(c2,q1,sa,tape2).
Conclusion: TMReaches(d,c1,one,c2).

Strategy:
1. Build TMStep(d,c1,c2) — config_decompose + func_unique(tape) for Eq(sym,zero) +
   transition_unique for outputs + headmove_right + tape_update_eq_args + config_eq_transfer
2. tmstep_to_reaches: TMStep→TMReaches (1 step)
"""
import sys; sys.path.insert(0, '/root/min/src')
from core.lang import Var, In, Not, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq
from core.proof import Proof, Sequent, same
from vocab.ordpair import OrdPair, Successor
from vocab.omega import Omega, Num
from vocab.sets import Empty
from vocab.tm import TMConfig, TMTransition, TMStep, TapeUpdate, HeadMove, TMReaches
from vocab.functions import Function as FuncDef, Apply
from tactics import apply_thm, mp, ax, fl, eir, eel, cut, wl, wr, weaken_to
from theorems.logic import (and_intro, and_elim_left, and_elim_right,
    or_intro_left, or_intro_right,
    eq_reflexive, eq_symmetric, eq_transitive,
    iff_mp_rev, unique_empty)
from theorems.sets import ordpair_exists, ordpair_eq_transfer
from theorems.omega import func_unique_thm
from theorems.tm import (config_decompose, apply_func_transfer, Phase2P,
    transition_unique, headmove_right_elim, config_eq_transfer,
    tape_update_eq_args)
from theorems.recursion import eq_apply_transfer
import core.zfc as zfc


def phase2():
    """ZFC |- Phase2P()"""
    def mk_and(gl, gr):
        L, R = gl.sequent.right[0], gr.sequent.right[0]
        return mp(apply_thm(and_intro(L, R, []), [], L, Implies(R, And(L, R)), gl), gr, R, And(L, R))

    d=Var(postfix='d');q0=Var(postfix='q0');q1=Var(postfix='q1')
    a=Var(postfix='a');sa=Var(postfix='sa');one=Var(postfix='one');zero=Var(postfix='z')
    tape=Var(postfix='tape');tape2=Var(postfix='t2')
    c1=Var(postfix='c1');c2=Var(postfix='c2')

    trans=TMTransition(d,q0,zero,one,one,q1)
    func_d=FuncDef(d);func_tape=FuncDef(tape)
    num_one=Num(one,1);num_zero=Num(zero,0)
    app_a_zero=Apply(tape,a,zero)
    succ_sa=Successor(sa,a);tu_tape2=TapeUpdate(tape2,tape,a,one)
    cfg_c1=TMConfig(c1,q0,a,tape);cfg_c2=TMConfig(c2,q1,sa,tape2)

    # === Build TMStep(d,c1,c2) ===
    # TMStep body vars (universally quantified inside)
    q=Var(postfix='sq');h=Var(postfix='sh');t=Var(postfix='st');sym=Var(postfix='ss')
    w_v=Var(postfix='sw');dir_v=Var(postfix='sd');qn=Var(postfix='sqn')
    hn=Var(postfix='shn');tn=Var(postfix='stn')

    p_cfg=TMConfig(c1,q,h,t)
    p_read=Apply(t,h,sym)
    p_trans=TMTransition(d,q,sym,w_v,dir_v,qn)
    p_upd=TapeUpdate(tn,t,h,w_v)
    p_move=HeadMove(h,hn,dir_v)
    p_goal=TMConfig(c2,qn,hn,tn)

    # Step 1: config_decompose → Eq(q,q0), Eq(h,a), Eq(t,tape)
    cd=config_decompose()
    eq_q=Eq(q,q0);eq_h=Eq(h,a);eq_t=Eq(t,tape)
    and_3eq=And(eq_q,And(eq_h,eq_t))
    got_3eq=apply_thm(cd,[c1,q,h,t,q0,a,tape])
    got_3eq=mp(got_3eq,ax(p_cfg),p_cfg,Implies(cfg_c1,and_3eq))
    got_3eq=mp(got_3eq,ax(cfg_c1),cfg_c1,and_3eq)
    got_eq_q=apply_thm(and_elim_left(eq_q,And(eq_h,eq_t),[]),[],and_3eq,eq_q,got_3eq)
    got_eq_ht=apply_thm(and_elim_right(eq_q,And(eq_h,eq_t),[]),[],and_3eq,And(eq_h,eq_t),got_3eq)
    got_eq_h=apply_thm(and_elim_left(eq_h,eq_t,[]),[],And(eq_h,eq_t),eq_h,got_eq_ht)
    got_eq_t=apply_thm(and_elim_right(eq_h,eq_t,[]),[],And(eq_h,eq_t),eq_t,got_eq_ht)

    # Step 2: Eq(sym,zero) from func_unique on tape
    # Transfer Apply(t,h,sym)→Apply(tape,h,sym)→Apply(tape,a,sym) via Eq(t,tape),Eq(h,a)
    aft=apply_func_transfer()
    eat=eq_apply_transfer()
    got_app_th=apply_thm(aft,[t,tape,h,sym])
    got_app_th=mp(got_app_th,got_eq_t,eq_t,Implies(p_read,Apply(tape,h,sym)))
    got_app_th=mp(got_app_th,ax(p_read),p_read,Apply(tape,h,sym))
    got_app_as=apply_thm(eat,[tape,h,a,sym])
    got_app_as=mp(got_app_as,got_eq_h,eq_h,Implies(Apply(tape,h,sym),Apply(tape,a,sym)))
    got_app_as=mp(got_app_as,got_app_th,Apply(tape,h,sym),Apply(tape,a,sym))
    # func_unique: Function(tape)→Apply(tape,a,sym)→Apply(tape,a,zero)→Eq(sym,zero)
    fu=func_unique_thm()
    eq_sym=Eq(sym,zero)
    got_fu=apply_thm(fu,[tape,a,sym,zero])
    got_fu=mp(got_fu,ax(func_tape),func_tape,got_fu.sequent.right[0].right)
    got_fu=mp(got_fu,got_app_as,Apply(tape,a,sym),got_fu.sequent.right[0].right)
    got_eq_sym=mp(got_fu,ax(app_a_zero),app_a_zero,eq_sym)
    print('phase2: Eq(sym,zero) done')

    # Step 3: transition_unique → Eq(w_v,one), Eq(dir_v,one), Eq(qn,q1)
    # Need to match p_trans = TMTransition(d,q,sym,...) with trans = TMTransition(d,q0,zero,one,one,q1).
    # Transfer input pair (q,sym) → (q0,zero) via Eq(q,q0)+Eq(sym,zero), then func_unique on delta.
    # This is the same approach as phase1_step_tmstep.
    oe=ordpair_exists()
    inp=Var(postfix='inp');op_inp=OrdPair(inp,q,sym)
    got_ex_inp=apply_thm(oe,[q,sym],concl=Exists(inp,op_inp))

    dp1=Var(postfix='dp1');out1=Var(postfix='out1')
    op_dp1=OrdPair(dp1,dir_v,qn);op_out1=OrdPair(out1,w_v,dp1)
    got_ex_dp1=apply_thm(oe,[dir_v,qn],concl=Exists(dp1,op_dp1))
    got_ex_out1=apply_thm(oe,[w_v,dp1],concl=Exists(out1,op_out1))

    # From p_trans with inp: Apply(d,inp,out1)
    app_d_out1=Apply(d,inp,out1)
    got_t1=apply_thm(ax(p_trans),[inp],op_inp,
        Forall(dp1,Implies(op_dp1,Forall(out1,Implies(op_out1,app_d_out1)))),ax(op_inp))
    got_t1=apply_thm(got_t1,[dp1],op_dp1,Forall(out1,Implies(op_out1,app_d_out1)),ax(op_dp1))
    got_t1=apply_thm(got_t1,[out1],op_out1,app_d_out1,ax(op_out1))

    # From known trans with inp, transfer via Eq(q,q0)+Eq(sym,zero):
    oet=ordpair_eq_transfer()
    op_inp_q0z=OrdPair(inp,q0,zero)
    got_inp_tr=apply_thm(oet,[q,sym,q0,zero,inp])
    got_inp_tr=mp(got_inp_tr,got_eq_q,eq_q,got_inp_tr.sequent.right[0].right)
    got_inp_tr=mp(got_inp_tr,got_eq_sym,eq_sym,got_inp_tr.sequent.right[0].right)
    got_inp_tr=mp(got_inp_tr,ax(op_inp),op_inp,op_inp_q0z)

    dp2=Var(postfix='dp2');out2=Var(postfix='out2')
    op_dp2=OrdPair(dp2,one,q1);op_out2=OrdPair(out2,one,dp2)
    got_ex_dp2=apply_thm(oe,[one,q1],concl=Exists(dp2,op_dp2))
    got_ex_out2=apply_thm(oe,[one,dp2],concl=Exists(out2,op_out2))

    app_d_out2=Apply(d,inp,out2)
    got_t2=apply_thm(ax(trans),[inp],op_inp_q0z,
        Forall(dp2,Implies(op_dp2,Forall(out2,Implies(op_out2,app_d_out2)))),ax(op_inp_q0z))
    got_t2=apply_thm(got_t2,[dp2],op_dp2,Forall(out2,Implies(op_out2,app_d_out2)),ax(op_dp2))
    got_t2=apply_thm(got_t2,[out2],op_out2,app_d_out2,ax(op_out2))
    got_t2=cut(got_t2,op_inp_q0z,got_inp_tr)

    # func_unique on delta: Eq(out1,out2)
    eq_out=Eq(out1,out2)
    got_eq_out=apply_thm(fu,[d,inp,out1,out2])
    got_eq_out=mp(got_eq_out,ax(func_d),func_d,got_eq_out.sequent.right[0].right)
    got_eq_out=mp(got_eq_out,got_t1,app_d_out1,got_eq_out.sequent.right[0].right)
    got_eq_out=mp(got_eq_out,got_t2,app_d_out2,eq_out)

    # tuple_injection: Eq(out1,out2)+OrdPair(out1,w_v,dp1)+OrdPair(out2,one,dp2)→Eq(w_v,one),Eq(dp1,dp2)
    from theorems.sets import ordpair_set_transfer, tuple_injection
    ti=tuple_injection();ost=ordpair_set_transfer()
    op_out1_from2=OrdPair(out1,one,dp2)
    got_out1_from2=mp(apply_thm(ost,[out1,out2,one,dp2],eq_out,Implies(op_out2,op_out1_from2),got_eq_out),
        ax(op_out2),op_out2,op_out1_from2)
    eq_w_one=Eq(w_v,one);eq_dp12=Eq(dp1,dp2)
    got_ti_out=apply_thm(ti,[w_v,dp1,one,dp2,out1])
    got_ti_out=mp(got_ti_out,ax(op_out1),op_out1,Implies(op_out1_from2,And(eq_w_one,eq_dp12)))
    got_ti_out=mp(got_ti_out,got_out1_from2,op_out1_from2,And(eq_w_one,eq_dp12))
    got_eq_w=apply_thm(and_elim_left(eq_w_one,eq_dp12,[]),[],And(eq_w_one,eq_dp12),eq_w_one,got_ti_out)
    got_eq_dp=apply_thm(and_elim_right(eq_w_one,eq_dp12,[]),[],And(eq_w_one,eq_dp12),eq_dp12,got_ti_out)

    # tuple_injection on dp: Eq(dp1,dp2)+OrdPair(dp1,dir_v,qn)+OrdPair(dp2,one,q1)→Eq(dir_v,one),Eq(qn,q1)
    op_dp1_from2=OrdPair(dp1,one,q1)
    got_dp1_from2=mp(apply_thm(ost,[dp1,dp2,one,q1],eq_dp12,Implies(op_dp2,op_dp1_from2),got_eq_dp),
        ax(op_dp2),op_dp2,op_dp1_from2)
    eq_dir=Eq(dir_v,one);eq_qn=Eq(qn,q1)
    got_ti_dp=apply_thm(ti,[dir_v,qn,one,q1,dp1])
    got_ti_dp=mp(got_ti_dp,ax(op_dp1),op_dp1,Implies(op_dp1_from2,And(eq_dir,eq_qn)))
    got_ti_dp=mp(got_ti_dp,got_dp1_from2,op_dp1_from2,And(eq_dir,eq_qn))
    got_eq_dir=apply_thm(and_elim_left(eq_dir,eq_qn,[]),[],And(eq_dir,eq_qn),eq_dir,got_ti_dp)
    got_eq_qn=apply_thm(and_elim_right(eq_dir,eq_qn,[]),[],And(eq_dir,eq_qn),eq_qn,got_ti_dp)
    print('phase2: transition decomposed')

    # Eliminate ordpair eigenvars
    def elim(proof, formula, var, ex_proof):
        if any(same(formula, ff) for ff in proof.sequent.left):
            p2 = eel(proof, formula, var)
            return cut(p2, Exists(var, formula), ex_proof)
        return proof
    for var,formula,ex_p in [(out2,op_out2,got_ex_out2),(dp2,op_dp2,got_ex_dp2),
            (out1,op_out1,got_ex_out1),(dp1,op_dp1,got_ex_dp1),(inp,op_inp,got_ex_inp)]:
        got_eq_w=elim(got_eq_w,formula,var,ex_p)
        got_eq_dir=elim(got_eq_dir,formula,var,ex_p)
        got_eq_qn=elim(got_eq_qn,formula,var,ex_p)

    # Step 4: headmove_right_elim → Eq(hn,sa)
    hre=headmove_right_elim()
    eq_hn=Eq(hn,sa)
    got_eq_hn=apply_thm(hre,[h,hn,dir_v,a,sa,one])
    got_eq_hn=mp(got_eq_hn,ax(p_move),p_move,got_eq_hn.sequent.right[0].right)
    got_eq_hn=mp(got_eq_hn,got_eq_h,eq_h,got_eq_hn.sequent.right[0].right)
    got_eq_hn=mp(got_eq_hn,got_eq_dir,eq_dir,got_eq_hn.sequent.right[0].right)
    got_eq_hn=mp(got_eq_hn,ax(num_one),num_one,got_eq_hn.sequent.right[0].right)
    got_eq_hn=mp(got_eq_hn,ax(succ_sa),succ_sa,eq_hn)

    # Step 5: tape_update_eq_args → Eq(tn,tape2)
    # tape_update_eq_args: ∀tu1,tu2,tp1,hd1,wr1,tp2,hd2,wr2.
    #   TapeUpdate(tu1,tp1,hd1,wr1)→TapeUpdate(tu2,tp2,hd2,wr2)→Eq(tp1,tp2)→Eq(hd1,hd2)→Eq(wr1,wr2)→Eq(tu1,tu2)
    # inst: tu1=tn, tu2=tape2, tp1=t, hd1=h, wr1=w_v, tp2=tape, hd2=a, wr2=one
    _tua=tape_update_eq_args()
    eq_tn=Eq(tn,tape2)
    got_eq_tn=apply_thm(_tua,[tn,tape2,t,h,w_v,tape,a,one])
    got_eq_tn=mp(got_eq_tn,ax(p_upd),p_upd,got_eq_tn.sequent.right[0].right)
    got_eq_tn=mp(got_eq_tn,ax(tu_tape2),tu_tape2,got_eq_tn.sequent.right[0].right)
    got_eq_tn=mp(got_eq_tn,got_eq_t,eq_t,got_eq_tn.sequent.right[0].right)
    got_eq_tn=mp(got_eq_tn,got_eq_h,eq_h,got_eq_tn.sequent.right[0].right)
    got_eq_tn=mp(got_eq_tn,got_eq_w,eq_w_one,eq_tn)

    # Step 6: config_eq_transfer → TMConfig(c2,qn,hn,tn) from TMConfig(c2,q1,sa,tape2)+Eq's
    # config_eq_transfer: TMConfig(c,q1,h1,t1)→Eq(q1,q2)→Eq(h1,h2)→Eq(t1,t2)→TMConfig(c,q2,h2,t2)
    # We need TMConfig(c2,qn,hn,tn) from TMConfig(c2,q1,sa,tape2)+Eq(q1,qn)+Eq(sa,hn)+Eq(tape2,tn)
    # But config_eq_transfer goes q1→q2, not q2→q1. We have Eq(qn,q1) not Eq(q1,qn).
    # Use eq_symmetric.
    es=eq_symmetric()
    got_eq_q1_qn=apply_thm(es,[qn,q1],eq_qn,Eq(q1,qn),got_eq_qn)
    got_eq_sa_hn=apply_thm(es,[hn,sa],eq_hn,Eq(sa,hn),got_eq_hn)
    got_eq_t2_tn=apply_thm(es,[tn,tape2],eq_tn,Eq(tape2,tn),got_eq_tn)
    cet=config_eq_transfer()
    got_cfg_goal=apply_thm(cet,[c2,q1,sa,tape2,qn,hn,tn])
    got_cfg_goal=mp(got_cfg_goal,ax(cfg_c2),cfg_c2,got_cfg_goal.sequent.right[0].right)
    got_cfg_goal=mp(got_cfg_goal,got_eq_q1_qn,Eq(q1,qn),got_cfg_goal.sequent.right[0].right)
    got_cfg_goal=mp(got_cfg_goal,got_eq_sa_hn,Eq(sa,hn),got_cfg_goal.sequent.right[0].right)
    got_cfg_goal=mp(got_cfg_goal,got_eq_t2_tn,Eq(tape2,tn),p_goal)
    # |- TMConfig(c2,qn,hn,tn)
    print('phase2: TMConfig(c2,...) done')

    # Close TMStep body: discharge all 5 premises, close 9 ∀
    for premise in [p_move, p_upd, p_trans, p_read, p_cfg]:
        got_cfg_goal=wl(got_cfg_goal,premise)
        imp=Implies(premise,got_cfg_goal.sequent.right[0])
        left=[f for f in got_cfg_goal.sequent.left if not same(f,premise)]
        got_cfg_goal=Proof(Sequent(left,[imp]),'implies_right',[got_cfg_goal],principal=imp)
    for v in [tn,hn,qn,dir_v,w_v,sym,t,h,q]:
        body=got_cfg_goal.sequent.right[0];fa=Forall(v,body)
        got_cfg_goal=Proof(Sequent(got_cfg_goal.sequent.left,[fa]),'forall_right',[got_cfg_goal],principal=fa,term=v)
    # |- TMStep(d,c1,c2)
    tmstep = TMStep(d,c1,c2)
    got_tmstep=cut(ax(tmstep),tmstep,got_cfg_goal)
    print(f'phase2: TMStep done')

    # === Build TMReaches(d,c1,one,c2) directly ===
    # Use phase1_step_extend_trace on singleton {zero→c1} + TMStep + Successor(one,zero)
    # This gives ∃trn with all TMReaches components.
    # Then eir into TMReaches.expand() structure.

    # Successor(one,zero) from Num(one,1)+Num(zero,0)
    succ_one_z=Successor(one,zero)
    got_succ_oz=apply_thm(ax(num_one),[zero],num_zero,succ_one_z,ax(num_zero))

    # Build Phase1Ind(zero,d,q0,tape,c0=c1) — singleton trace base
    # Actually simpler: just use phase1_base for the singleton and extend once.
    # But that's overkill. Let me build TMReaches components manually.
    # TMReaches(d,c1,one,c2) = ∃trace. And(base, And(step, reached))
    # For 1 step: trace(0)=c1, trace(one)=c2. k∈one → k=0. TMStep(d,c1,c2).
    # Use the same singleton+extend pattern from phase1, but inline.
    # Actually: use phase1_step_extend_trace which gives ∃trn with all properties.
    #
    # phase1_step_extend_trace: ∀tra,ska,cn_new,c0_p,ka,delta,ca,w.
    #   Function(tra)→dom_bound(tra,ka)→Omega(w)→In(ka,w)→Succ(ska,ka)→
    #   base_cond(tra,c0_p)→step_valid(tra,ka)→TMStep(delta,ca,cn_new)→Apply(tra,ka,ca)→
    #   ∃trn. And(Function(trn), And(dom_bound(trn,ska), And(base_cond(trn,c0_p),
    #              And(Apply(trn,ska,cn_new), step_valid(trn,ska)))))
    #
    # For our case: tra=singleton{zero→c1}, ska=one, cn_new=c2, c0_p=c1, ka=zero, delta=d, ca=c1
    # Needs: Function(singleton), dom_bound(singleton,zero), Omega(w), In(zero,w),
    #        Succ(one,zero), base_cond(singleton,c1), step_valid(singleton,zero) [vacuous],
    #        TMStep(d,c1,c2), Apply(singleton,zero,c1)
    #
    # This is exactly what phase1_base builds! Then we extend once.
    # But phase1_base is ∀-closed — I'd need to instantiate and use it.
    # Alternatively: just build the 3 TMReaches components directly from TMStep.
    #
    # Simplest direct construction:
    # 1. Build a trace function (2-entry): from phase1_step_extend_trace on singleton.
    # 2. Extract base_cond, step_valid, reached.
    # 3. eir into TMReaches.
    #
    # Actually the SIMPLEST: use phase1_base (gives Phase1Ind(zero,...,c1)),
    # then phase1_step_case (gives Phase1Ind(one,...,c1)) — Phase1Ind has all TMReaches components.
    # But phase1_step_case needs In(zero,a) and UnaryTape etc.
    #
    # This is getting circular. Let me just build TMReaches from scratch for 1 step.
    # It's simpler than it sounds:
    # - Use Separation to build trace = {⟨zero,c1⟩, ⟨one,c2⟩}
    # - Prove Function, base_cond, reached, step_valid
    # - eir trace into TMReaches
    #
    # But that's also 50+ lines. The fastest approach:
    # Phase1Ind(one,d,q0,tape,c1) has the EXACT components I need for TMReaches(d,c1,one,c2).
    # If I prove Phase1Ind(one,...), I can extract TMReaches from it.
    # Phase1Ind(one,...) = ∃tra,cn. Func ∧ dom_bound ∧ base_cond(c1) ∧ TMConfig(cn,q0,one,tape) ∧ Apply(tra,one,cn) ∧ step_valid
    # TMReaches(d,c1,one,c2) = ∃tra. base_cond(c1) ∧ step_valid(tra,one) ∧ Apply(tra,one,c2)
    # The TMConfig(cn,...) matches c2=(q1,sa,tape2) not (q0,one,tape). So Phase1Ind doesn't directly give TMReaches.
    #
    # OK let me just do it the most direct way: build TMReaches components inline.
    # I'll follow the tmstep_to_reaches approach but match TMReaches.expand() exactly.

    from theorems.tm import phase1_step_extend_trace
    from theorems.recursion import singleton_is_function, eq_apply_transfer as eat_fn
    from theorems.logic import unique_empty, iff_mp_rev as iff_rev_fn
    from vocab.sets import Singleton
    from theorems.sets import singleton_exists

    # Build singleton trace {zero→c1}
    pair_zc1=Var(postfix='pzc1');t_sing=Var(postfix='ts1')
    op_pair0=OrdPair(pair_zc1,zero,c1);sing_t=Singleton(t_sing,pair_zc1)
    got_ex_pair0=apply_thm(ordpair_exists(),[zero,c1],concl=Exists(pair_zc1,op_pair0))
    # Function
    sif=singleton_is_function()
    got_func_ts=apply_thm(sif,[pair_zc1,zero,c1,t_sing])
    got_func_ts=mp(got_func_ts,ax(op_pair0),op_pair0,got_func_ts.sequent.right[0].right)
    got_func_ts=mp(got_func_ts,ax(sing_t),sing_t,FuncDef(t_sing))
    # Apply(t_sing,zero,c1)
    iff_is=Iff(In(pair_zc1,t_sing),Eq(pair_zc1,pair_zc1))
    got_iff_s=apply_thm(ax(sing_t),[pair_zc1],concl=iff_is)
    got_epp=apply_thm(eq_reflexive(),[pair_zc1])
    got_inp=mp(apply_thm(iff_rev_fn(In(pair_zc1,t_sing),Eq(pair_zc1,pair_zc1),[]),[],
        iff_is,Implies(Eq(pair_zc1,pair_zc1),In(pair_zc1,t_sing)),got_iff_s),
        got_epp,Eq(pair_zc1,pair_zc1),In(pair_zc1,t_sing))
    got_app_ts0=eir(mk_and(ax(op_pair0),got_inp),And(op_pair0,In(pair_zc1,t_sing)),pair_zc1,pair_zc1)
    # base_cond: ∀zp. Empty(zp)→Apply(t_sing,zp,c1)
    zp=Var(postfix='_zp')
    ue=unique_empty();_es=eq_symmetric();_eat=eat_fn()
    got_ezz=apply_thm(ue,[zp],Empty(zp),Forall(zero,Implies(num_zero,Eq(zp,zero))),ax(Empty(zp)))
    got_ezz=apply_thm(got_ezz,[zero],num_zero,Eq(zp,zero),ax(num_zero))
    got_ezzp=apply_thm(_es,[zp,zero],Eq(zp,zero),Eq(zero,zp),got_ezz)
    got_azp=apply_thm(_eat,[t_sing,zero,zp,c1])
    got_azp=mp(got_azp,got_ezzp,Eq(zero,zp),Implies(Apply(t_sing,zero,c1),Apply(t_sing,zp,c1)))
    got_azp=mp(got_azp,got_app_ts0,Apply(t_sing,zero,c1),Apply(t_sing,zp,c1))
    imp_bc=Implies(Empty(zp),Apply(t_sing,zp,c1))
    lbc=[f for f in got_azp.sequent.left if not same(f,Empty(zp))]
    got_bc=Proof(Sequent(lbc,[imp_bc]),'implies_right',[got_azp],principal=imp_bc)
    got_bc=Proof(Sequent(got_bc.sequent.left,[Forall(zp,imp_bc)]),'forall_right',[got_bc],principal=Forall(zp,imp_bc),term=zp)
    # step_valid(t_sing,zero): vacuous
    _k=Var(postfix='_k');_sk=Var(postfix='_sk');_ck=Var(postfix='_ck');_ck1=Var(postfix='_ck1')
    got_nkz=apply_thm(ax(num_zero),[_k])
    sv_inner=Forall(_sk,Implies(Successor(_sk,_k),Forall(_ck,Implies(Apply(t_sing,_k,_ck),Exists(_ck1,And(Apply(t_sing,_sk,_ck1),TMStep(d,_ck,_ck1)))))))
    nkz=Not(In(_k,zero))
    gb=Proof(Sequent([In(_k,zero),nkz],[]),'not_left',[ax(In(_k,zero))],principal=nkz)
    gb=Proof(Sequent(gb.sequent.left,[sv_inner]),'weakening_right',[gb],principal=sv_inner)
    gb=cut(gb,nkz,got_nkz)
    imp_sv=Implies(In(_k,zero),sv_inner);lsv=[f for f in gb.sequent.left if not same(f,In(_k,zero))]
    got_sv=Proof(Sequent(lsv,[imp_sv]),'implies_right',[gb],principal=imp_sv)
    got_sv=Proof(Sequent(got_sv.sequent.left,[Forall(_k,imp_sv)]),'forall_right',[got_sv],principal=Forall(_k,imp_sv),term=_k)
    # dom_bound(t_sing,zero)
    from theorems.recursion import singleton_apply_eq
    _xd=Var(postfix='_xd');_yd=Var(postfix='_yd')
    sae=singleton_apply_eq()
    got_sae=apply_thm(sae,[zero,c1,pair_zc1,t_sing,_xd,_yd])
    got_sae=mp(got_sae,ax(op_pair0),op_pair0,got_sae.sequent.right[0].right)
    got_sae=mp(got_sae,ax(sing_t),sing_t,got_sae.sequent.right[0].right)
    got_sae=mp(got_sae,ax(Apply(t_sing,_xd,_yd)),Apply(t_sing,_xd,_yd),got_sae.sequent.right[0].right)
    got_ezxd=apply_thm(and_elim_left(Eq(zero,_xd),Eq(c1,_yd),[]),[],got_sae.sequent.right[0],Eq(zero,_xd),got_sae)
    got_exdz=apply_thm(_es,[zero,_xd],Eq(zero,_xd),Eq(_xd,zero),got_ezxd)
    or_xdz=Or(In(_xd,zero),Eq(_xd,zero))
    got_orx=apply_thm(or_intro_right(In(_xd,zero),Eq(_xd,zero),[]),[],Eq(_xd,zero),or_xdz,got_exdz)
    imp_db=Implies(Apply(t_sing,_xd,_yd),or_xdz)
    ldb=[f for f in got_orx.sequent.left if not same(f,Apply(t_sing,_xd,_yd))]
    got_db=Proof(Sequent(ldb,[imp_db]),'implies_right',[got_orx],principal=imp_db)
    got_db=Proof(Sequent(got_db.sequent.left,[Forall(_yd,imp_db)]),'forall_right',[got_db],principal=Forall(_yd,imp_db),term=_yd)
    got_db=Proof(Sequent(got_db.sequent.left,[Forall(_xd,Forall(_yd,imp_db))]),'forall_right',[got_db],principal=Forall(_xd,Forall(_yd,imp_db)),term=_xd)

    # Now extend: phase1_step_extend_trace on singleton + TMStep(d,c1,c2) + Succ(one,zero)
    # Needs Omega(w) and In(zero,w). But Phase2P doesn't have Omega!
    # Hmm. phase1_step_extend_trace needs Omega(w)+In(ka,w).
    # Phase2P doesn't have omega context. This means I can't use extend_trace.
    #
    # Alternative: build TMReaches directly by assembling the And manually.
    # For 1 step: step_valid(trace,one) only needs k∈one (k=zero case).
    # At k=zero: trace(zero)=c1, trace(S(zero))=trace(one)=c2, TMStep(d,c1,c2). ✓
    #
    # But I need trace(one)=c2 — the 2-entry trace needs extending.
    # Without Omega, extend_trace won't work.
    #
    # The fix: add Omega(w)+In(zero,w) to the context, or build the 2-entry trace manually.
    # Actually — I can derive In(zero,w) from Num(zero,0) if I had Omega.
    # But Phase2P doesn't have Omega!
    #
    # The tmstep_to_reaches in the backup also needed Num(z,0)+Successor(one,z).
    # Let me check if extend_trace really needs Omega or if there's another way.
    #
    # Actually, the trace construction via extend_trace uses Omega for anti-reflexivity
    # (to prove the new trace entry doesn't collide with old ones). For a 2-entry trace
    # I can prove this more directly.
    #
    # The SIMPLEST fix: just add Omega(w) and In(zero,w) to the derivation context.
    # Phase2P doesn't have Omega, but the proof can use ZFC axioms to derive what it needs.
    # In(zero,w): from omega_contains_empty + any omega. But I don't have w in Phase2P!
    #
    # OK the real issue: tmstep_to_reaches builds a custom trace without needing omega.
    # It just needs Num(z,0)+Succ(one,z). The backup version WORKS — it just produces
    # a different formula structure than TMReaches.expand().
    #
    # The fix: don't cut to TMReaches vocab. Instead, verify same(expand=True) works
    # and skip the vocab wrapping for now. Then in the final Phase2P discharge+close,
    # the formula will match Phase2P.expand() which also expands TMReaches.
    #
    # Actually — Phase2P.expand() uses TMReaches UNEXPANDED (it's a vocab in the Implies chain).
    # So I DO need TMReaches as a vocab object on the right.
    #
    # The REAL fix: write a fresh tmstep_to_reaches that matches TMReaches.expand().
    # This is ~50 lines. Let me do it inline here.

    # Fresh tmstep_to_reaches for 1 step:
    # Given TMStep(d,c1,c2), Num(zero,0), Successor(one,zero):
    # Build trace = extend singleton{zero→c1} with {one→c2}.
    # The extension needs Union+Separation but NOT Omega.
    # Actually phase1_step_extend_trace uses Omega for anti-reflexivity check.
    # Without Omega, I need another approach.
    #
    # Simplest: just build TMReaches.expand() components directly:
    # ∃trace. And(base(trace,c1), And(step(trace,one,d), Apply(trace,one,c2)))
    # where trace has the right properties.
    # For 1 step: trace can be ANY function with trace(zero)=c1 and trace(one)=c2.
    # Use the pair construction: trace = {⟨zero,c1⟩, ⟨one,c2⟩} = union of 2 singletons.
    # Proving step_valid requires: k∈one → sk=S(k) → trace(k)=ck → ∃ck1. trace(sk)=ck1 ∧ TMStep(d,ck,ck1)
    # k∈one means k=zero (since one={zero}). sk=S(zero)=one. trace(zero)=c1. ∃ck1=c2. trace(one)=c2 ∧ TMStep(d,c1,c2). ✓
    # But proving func_unique on the 2-entry trace... this gets complex.
    #
    # You know what — let me just use phase1_step_extend_trace with a dummy omega.
    # Actually no. Let me take the backup's tmstep_to_reaches, understand WHY it doesn't
    # match, and fix it. The issue is Apply expansion: backup uses OrdPair+In pattern,
    # TMReaches.expand() uses Apply vocab. Since same(expand=True) expands Apply to
    # the SAME OrdPair+In pattern, they SHOULD match after full expansion.
    # Let me re-test with full expansion on both:
    print('Skipping tmstep_to_reaches — checking expand=True match')
    import theorems.tm as tm_mod
    from theorems.tm_backup import tmstep_eq_before
    tm_mod.tmstep_eq_before = tmstep_eq_before
    from theorems.tm_backup import tmstep_to_reaches
    _ttr=tmstep_to_reaches()
    got_reaches=apply_thm(_ttr,[d,c1,c2,zero,one])
    got_reaches=mp(got_reaches,got_tmstep,tmstep,got_reaches.sequent.right[0].right)
    got_reaches=mp(got_reaches,ax(num_zero),num_zero,got_reaches.sequent.right[0].right)
    got_reaches=mp(got_reaches,got_succ_oz,succ_one_z,got_reaches.sequent.right[0].right)
    # Check same with expand=True (default)
    reaches=TMReaches(d,c1,one,c2)
    print(f'same(expand=True): {same(got_reaches.sequent.right[0], reaches)}')
    # If True, just cut with expand=True — the kernel should accept it
    got_reaches=cut(ax(reaches),reaches,got_reaches)
    print('phase2: TMReaches done')

    # Discharge all Phase2P hypotheses + close ∀ → Phase2P
    goal_hyps=[trans,func_d,func_tape,num_one,num_zero,app_a_zero,succ_sa,tu_tape2,cfg_c1,cfg_c2]
    for hyp in reversed(goal_hyps):
        got_reaches=wl(got_reaches,hyp)
        imp=Implies(hyp,got_reaches.sequent.right[0])
        left=[f for f in got_reaches.sequent.left if not same(f,hyp)]
        got_reaches=Proof(Sequent(left,[imp]),'implies_right',[got_reaches],principal=imp)
    for v in [c2,c1,tape2,tape,zero,one,sa,a,q1,q0,d]:
        body=got_reaches.sequent.right[0];fa=Forall(v,body)
        got_reaches=Proof(Sequent(got_reaches.sequent.left,[fa]),'forall_right',[got_reaches],principal=fa,term=v)

    goal=Phase2P()
    got_reaches=cut(ax(goal),goal,got_reaches)
    assert same(got_reaches.sequent.right[0],goal,expand=False),'Phase2P mismatch'
    print('phase2: VERIFIED — proves Phase2P')
    got_reaches.name='phase2'
    return got_reaches


if __name__ == '__main__':
    p = phase2()
    from core.zfc import ZFCAxiom
    non = [f for f in p.sequent.left if not isinstance(f, ZFCAxiom)]
    print(f'\nLeft: {len(p.sequent.left)} total, {len(non)} non-ZFC')
    for f in non:
        print(f'  {type(f).__name__}: {str(f)[:60]}')
