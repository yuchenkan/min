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
    eq_reflexive, eq_symmetric, eq_transitive)
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

    # === tmstep_to_reaches: TMStep(d,c1,c2)→Num(z,0)→Successor(one,z)→TMReaches(d,c1,one,c2) ===
    # Need Successor(one,zero). From Num(one,1): ∀m. Num(m,0)→Successor(one,m). Inst m=zero.
    succ_one_z=Successor(one,zero)
    got_succ_oz=apply_thm(ax(num_one),[zero],num_zero,succ_one_z,ax(num_zero))
    # tmstep_to_reaches: need it from tm_backup (or move it)
    # For now, import from backup with monkey-patch
    import theorems.tm as tm_mod
    from theorems.tm_backup import tmstep_eq_before
    tm_mod.tmstep_eq_before = tmstep_eq_before
    from theorems.tm_backup import tmstep_to_reaches
    _ttr=tmstep_to_reaches()
    got_reaches=apply_thm(_ttr,[d,c1,c2,zero,one])
    got_reaches=mp(got_reaches,got_tmstep,tmstep,got_reaches.sequent.right[0].right)
    got_reaches=mp(got_reaches,ax(num_zero),num_zero,got_reaches.sequent.right[0].right)
    got_reaches=mp(got_reaches,got_succ_oz,succ_one_z,got_reaches.sequent.right[0].right)
    # |- TMReaches(d,c1,one,c2)
    reaches=TMReaches(d,c1,one,c2)
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
