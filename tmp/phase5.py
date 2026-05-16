"""Phase5P proof — single TMStep: (q2,c,tape2)→(qH,hf,tf). Move right, erase last 1."""
import sys; sys.path.insert(0, '/root/min/src')
from core.lang import Var, In, Not, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq
from core.proof import Proof, Sequent, same
from vocab.ordpair import OrdPair, Successor
from vocab.omega import Omega, Num
from vocab.tm import TMConfig, TMTransition, TMStep, TapeUpdate, HeadMove, TMReaches
from vocab.functions import Function as FuncDef, Apply
from tactics import apply_thm, mp, ax, fl, eir, eel, cut, wl, wr, weaken_to
from theorems.logic import (and_intro, and_elim_left, and_elim_right,
    eq_reflexive, eq_symmetric, eq_transitive)
from theorems.sets import (ordpair_exists, ordpair_eq_transfer, ordpair_set_transfer, tuple_injection)
from theorems.omega import func_unique_thm, omega_contains_empty, omega_exists
from theorems.tm import (Phase5P, config_decompose, apply_func_transfer,
    headmove_right_elim, config_eq_transfer, tape_update_eq_args, tmstep_to_reaches)
from theorems.recursion import eq_apply_transfer
import core.zfc as zfc


def phase5():
    """ZFC |- Phase5P()"""
    def mk_and(gl, gr):
        L, R = gl.sequent.right[0], gr.sequent.right[0]
        return mp(apply_thm(and_intro(L, R, []), [], L, Implies(R, And(L, R)), gl), gr, R, And(L, R))

    d=Var(postfix='d');q2v=Var(postfix='q2');qH=Var(postfix='qH')
    c=Var(postfix='c');hf=Var(postfix='hf');one=Var(postfix='one');zero=Var(postfix='z')
    tape2=Var(postfix='t2');tf=Var(postfix='tf')
    c1=Var(postfix='c1');c2=Var(postfix='c2')

    trans=TMTransition(d,q2v,one,zero,one,qH)
    func_d=FuncDef(d);func_tape2=FuncDef(tape2)
    num_one=Num(one,1);num_zero=Num(zero,0)
    succ_hf=Successor(hf,c);app_c_one=Apply(tape2,c,one)
    tu_tf=TapeUpdate(tf,tape2,c,zero)
    cfg_c1=TMConfig(c1,q2v,c,tape2);cfg_c2=TMConfig(c2,qH,hf,tf)

    # TMStep body vars
    q=Var(postfix='sq');h=Var(postfix='sh');t=Var(postfix='st');sym=Var(postfix='ss')
    w_v=Var(postfix='sw');dir_v=Var(postfix='sd');qn=Var(postfix='sqn')
    hn=Var(postfix='shn');tn=Var(postfix='stn')
    p_cfg=TMConfig(c1,q,h,t);p_read=Apply(t,h,sym)
    p_trans=TMTransition(d,q,sym,w_v,dir_v,qn)
    p_upd=TapeUpdate(tn,t,h,w_v);p_move=HeadMove(h,hn,dir_v)
    p_goal=TMConfig(c2,qn,hn,tn)

    # Step 1: config_decompose → Eq(q,q2), Eq(h,c), Eq(t,tape2)
    cd=config_decompose()
    eq_q=Eq(q,q2v);eq_h=Eq(h,c);eq_t=Eq(t,tape2)
    and_3eq=And(eq_q,And(eq_h,eq_t))
    got_3eq=apply_thm(cd,[c1,q,h,t,q2v,c,tape2])
    got_3eq=mp(got_3eq,ax(p_cfg),p_cfg,Implies(cfg_c1,and_3eq))
    got_3eq=mp(got_3eq,ax(cfg_c1),cfg_c1,and_3eq)
    got_eq_q=apply_thm(and_elim_left(eq_q,And(eq_h,eq_t),[]),[],and_3eq,eq_q,got_3eq)
    got_eq_ht=apply_thm(and_elim_right(eq_q,And(eq_h,eq_t),[]),[],and_3eq,And(eq_h,eq_t),got_3eq)
    got_eq_h=apply_thm(and_elim_left(eq_h,eq_t,[]),[],And(eq_h,eq_t),eq_h,got_eq_ht)
    got_eq_t=apply_thm(and_elim_right(eq_h,eq_t,[]),[],And(eq_h,eq_t),eq_t,got_eq_ht)

    # Step 2: Eq(sym,one) via func_unique on tape2
    aft=apply_func_transfer();eat=eq_apply_transfer()
    got_app_th=apply_thm(aft,[t,tape2,h,sym])
    got_app_th=mp(got_app_th,got_eq_t,eq_t,Implies(p_read,Apply(tape2,h,sym)))
    got_app_th=mp(got_app_th,ax(p_read),p_read,Apply(tape2,h,sym))
    got_app_cs=apply_thm(eat,[tape2,h,c,sym])
    got_app_cs=mp(got_app_cs,got_eq_h,eq_h,Implies(Apply(tape2,h,sym),Apply(tape2,c,sym)))
    got_app_cs=mp(got_app_cs,got_app_th,Apply(tape2,h,sym),Apply(tape2,c,sym))
    fu=func_unique_thm();eq_sym=Eq(sym,one)
    got_fu=apply_thm(fu,[tape2,c,sym,one])
    got_fu=mp(got_fu,ax(func_tape2),func_tape2,got_fu.sequent.right[0].right)
    got_fu=mp(got_fu,got_app_cs,Apply(tape2,c,sym),got_fu.sequent.right[0].right)
    got_eq_sym=mp(got_fu,ax(app_c_one),app_c_one,eq_sym)
    print('phase5: Eq(sym,one) done')

    # Step 3: transition decomposition → Eq(w_v,zero), Eq(dir_v,one), Eq(qn,qH)
    oe=ordpair_exists()
    inp=Var(postfix='inp');op_inp=OrdPair(inp,q,sym)
    got_ex_inp=apply_thm(oe,[q,sym],concl=Exists(inp,op_inp))
    dp1=Var(postfix='dp1');out1=Var(postfix='out1')
    op_dp1=OrdPair(dp1,dir_v,qn);op_out1=OrdPair(out1,w_v,dp1)
    got_ex_dp1=apply_thm(oe,[dir_v,qn],concl=Exists(dp1,op_dp1))
    got_ex_out1=apply_thm(oe,[w_v,dp1],concl=Exists(out1,op_out1))
    app_d_out1=Apply(d,inp,out1)
    got_t1=apply_thm(ax(p_trans),[inp],op_inp,
        Forall(dp1,Implies(op_dp1,Forall(out1,Implies(op_out1,app_d_out1)))),ax(op_inp))
    got_t1=apply_thm(got_t1,[dp1],op_dp1,Forall(out1,Implies(op_out1,app_d_out1)),ax(op_dp1))
    got_t1=apply_thm(got_t1,[out1],op_out1,app_d_out1,ax(op_out1))
    # Transfer inp (q,sym)→(q2,one) via Eq(q,q2)+Eq(sym,one)
    oet=ordpair_eq_transfer()
    op_inp_q2one=OrdPair(inp,q2v,one)
    got_inp_tr=apply_thm(oet,[q,sym,q2v,one,inp])
    got_inp_tr=mp(got_inp_tr,got_eq_q,eq_q,got_inp_tr.sequent.right[0].right)
    got_inp_tr=mp(got_inp_tr,got_eq_sym,eq_sym,got_inp_tr.sequent.right[0].right)
    got_inp_tr=mp(got_inp_tr,ax(op_inp),op_inp,op_inp_q2one)
    # Known transition: TMTransition(d,q2,one,zero,one,qH)
    dp2=Var(postfix='dp2');out2=Var(postfix='out2')
    op_dp2=OrdPair(dp2,one,qH);op_out2=OrdPair(out2,zero,dp2)
    got_ex_dp2=apply_thm(oe,[one,qH],concl=Exists(dp2,op_dp2))
    got_ex_out2=apply_thm(oe,[zero,dp2],concl=Exists(out2,op_out2))
    app_d_out2=Apply(d,inp,out2)
    got_t2=apply_thm(ax(trans),[inp],op_inp_q2one,
        Forall(dp2,Implies(op_dp2,Forall(out2,Implies(op_out2,app_d_out2)))),ax(op_inp_q2one))
    got_t2=apply_thm(got_t2,[dp2],op_dp2,Forall(out2,Implies(op_out2,app_d_out2)),ax(op_dp2))
    got_t2=apply_thm(got_t2,[out2],op_out2,app_d_out2,ax(op_out2))
    got_t2=cut(got_t2,op_inp_q2one,got_inp_tr)
    eq_out=Eq(out1,out2)
    got_eq_out=apply_thm(fu,[d,inp,out1,out2])
    got_eq_out=mp(got_eq_out,ax(func_d),func_d,got_eq_out.sequent.right[0].right)
    got_eq_out=mp(got_eq_out,got_t1,app_d_out1,got_eq_out.sequent.right[0].right)
    got_eq_out=mp(got_eq_out,got_t2,app_d_out2,eq_out)
    ti=tuple_injection();ost=ordpair_set_transfer()
    op_out1_from2=OrdPair(out1,zero,dp2)
    got_o1f2=mp(apply_thm(ost,[out1,out2,zero,dp2],eq_out,Implies(op_out2,op_out1_from2),got_eq_out),
        ax(op_out2),op_out2,op_out1_from2)
    eq_w_zero=Eq(w_v,zero);eq_dp12=Eq(dp1,dp2)
    got_ti_out=apply_thm(ti,[w_v,dp1,zero,dp2,out1])
    got_ti_out=mp(got_ti_out,ax(op_out1),op_out1,Implies(op_out1_from2,And(eq_w_zero,eq_dp12)))
    got_ti_out=mp(got_ti_out,got_o1f2,op_out1_from2,And(eq_w_zero,eq_dp12))
    got_eq_w=apply_thm(and_elim_left(eq_w_zero,eq_dp12,[]),[],And(eq_w_zero,eq_dp12),eq_w_zero,got_ti_out)
    got_eq_dp=apply_thm(and_elim_right(eq_w_zero,eq_dp12,[]),[],And(eq_w_zero,eq_dp12),eq_dp12,got_ti_out)
    op_dp1_from2=OrdPair(dp1,one,qH)
    got_dp1f2=mp(apply_thm(ost,[dp1,dp2,one,qH],eq_dp12,Implies(op_dp2,op_dp1_from2),got_eq_dp),
        ax(op_dp2),op_dp2,op_dp1_from2)
    eq_dir=Eq(dir_v,one);eq_qn=Eq(qn,qH)
    got_ti_dp=apply_thm(ti,[dir_v,qn,one,qH,dp1])
    got_ti_dp=mp(got_ti_dp,ax(op_dp1),op_dp1,Implies(op_dp1_from2,And(eq_dir,eq_qn)))
    got_ti_dp=mp(got_ti_dp,got_dp1f2,op_dp1_from2,And(eq_dir,eq_qn))
    got_eq_dir=apply_thm(and_elim_left(eq_dir,eq_qn,[]),[],And(eq_dir,eq_qn),eq_dir,got_ti_dp)
    got_eq_qn=apply_thm(and_elim_right(eq_dir,eq_qn,[]),[],And(eq_dir,eq_qn),eq_qn,got_ti_dp)
    def elim(proof,formula,var,ex_proof):
        if any(same(formula,ff) for ff in proof.sequent.left):
            return cut(eel(proof,formula,var),Exists(var,formula),ex_proof)
        return proof
    for var,formula,ex_p in [(out2,op_out2,got_ex_out2),(dp2,op_dp2,got_ex_dp2),
            (out1,op_out1,got_ex_out1),(dp1,op_dp1,got_ex_dp1),(inp,op_inp,got_ex_inp)]:
        got_eq_w=elim(got_eq_w,formula,var,ex_p)
        got_eq_dir=elim(got_eq_dir,formula,var,ex_p)
        got_eq_qn=elim(got_eq_qn,formula,var,ex_p)
    print('phase5: transition decomposed')

    # Step 4: headmove_right_elim → Eq(hn,hf)
    hre=headmove_right_elim()
    eq_hn=Eq(hn,hf)
    got_eq_hn=apply_thm(hre,[h,hn,dir_v,c,hf,one])
    got_eq_hn=mp(got_eq_hn,ax(p_move),p_move,got_eq_hn.sequent.right[0].right)
    got_eq_hn=mp(got_eq_hn,got_eq_h,eq_h,got_eq_hn.sequent.right[0].right)
    got_eq_hn=mp(got_eq_hn,got_eq_dir,eq_dir,got_eq_hn.sequent.right[0].right)
    got_eq_hn=mp(got_eq_hn,ax(num_one),num_one,got_eq_hn.sequent.right[0].right)
    got_eq_hn=mp(got_eq_hn,ax(succ_hf),succ_hf,eq_hn)

    # Step 5: tape_update_eq_args → Eq(tn,tf)
    _tua=tape_update_eq_args()
    eq_tn=Eq(tn,tf)
    got_eq_tn=apply_thm(_tua,[tn,tf,t,h,w_v,tape2,c,zero])
    got_eq_tn=mp(got_eq_tn,ax(p_upd),p_upd,got_eq_tn.sequent.right[0].right)
    got_eq_tn=mp(got_eq_tn,ax(tu_tf),tu_tf,got_eq_tn.sequent.right[0].right)
    got_eq_tn=mp(got_eq_tn,got_eq_t,eq_t,got_eq_tn.sequent.right[0].right)
    got_eq_tn=mp(got_eq_tn,got_eq_h,eq_h,got_eq_tn.sequent.right[0].right)
    got_eq_tn=mp(got_eq_tn,got_eq_w,eq_w_zero,eq_tn)
    print('phase5: Eq(tn,tf) done')

    # Step 6: config_eq_transfer → TMConfig(c2,qn,hn,tn) from TMConfig(c2,qH,hf,tf)+Eq's
    _es=eq_symmetric()
    got_eq_qH_qn=apply_thm(_es,[qn,qH],eq_qn,Eq(qH,qn),got_eq_qn)
    got_eq_hf_hn=apply_thm(_es,[hn,hf],eq_hn,Eq(hf,hn),got_eq_hn)
    got_eq_tf_tn=apply_thm(_es,[tn,tf],eq_tn,Eq(tf,tn),got_eq_tn)
    cet=config_eq_transfer()
    got_cfg=apply_thm(cet,[c2,qH,hf,tf,qn,hn,tn])
    got_cfg=mp(got_cfg,ax(cfg_c2),cfg_c2,got_cfg.sequent.right[0].right)
    got_cfg=mp(got_cfg,got_eq_qH_qn,Eq(qH,qn),got_cfg.sequent.right[0].right)
    got_cfg=mp(got_cfg,got_eq_hf_hn,Eq(hf,hn),got_cfg.sequent.right[0].right)
    got_cfg=mp(got_cfg,got_eq_tf_tn,Eq(tf,tn),p_goal)
    print('phase5: TMConfig(c2,...) done')

    # Close TMStep
    for premise in [p_move,p_upd,p_trans,p_read,p_cfg]:
        got_cfg=wl(got_cfg,premise);imp=Implies(premise,got_cfg.sequent.right[0])
        left=[f for f in got_cfg.sequent.left if not same(f,premise)]
        got_cfg=Proof(Sequent(left,[imp]),'implies_right',[got_cfg],principal=imp)
    for v in [tn,hn,qn,dir_v,w_v,sym,t,h,q]:
        body=got_cfg.sequent.right[0];fa=Forall(v,body)
        got_cfg=Proof(Sequent(got_cfg.sequent.left,[fa]),'forall_right',[got_cfg],principal=fa,term=v)
    tmstep=TMStep(d,c1,c2)
    got_tmstep=cut(ax(tmstep),tmstep,got_cfg)
    print('phase5: TMStep done')

    # TMStep → TMReaches
    succ_one_z=Successor(one,zero)
    got_succ_oz=apply_thm(ax(num_one),[zero],num_zero,succ_one_z,ax(num_zero))
    # Need Omega(w) + In(zero,w). Use fresh w.
    w=Var(postfix='w_');omega_w=Omega(w)
    oce=omega_contains_empty()
    got_zw=apply_thm(oce,[w],omega_w,Forall(zero,Implies(num_zero,In(zero,w))),ax(omega_w))
    got_zw=apply_thm(got_zw,[zero],num_zero,In(zero,w),ax(num_zero))
    _ttr=tmstep_to_reaches()
    got_reaches=apply_thm(_ttr,[d,c1,c2,zero,one,w])
    got_reaches=mp(got_reaches,got_tmstep,tmstep,got_reaches.sequent.right[0].right)
    got_reaches=mp(got_reaches,ax(num_zero),num_zero,got_reaches.sequent.right[0].right)
    got_reaches=mp(got_reaches,got_succ_oz,succ_one_z,got_reaches.sequent.right[0].right)
    got_reaches=mp(got_reaches,ax(omega_w),omega_w,got_reaches.sequent.right[0].right)
    got_reaches=mp(got_reaches,got_zw,In(zero,w),got_reaches.sequent.right[0].right)
    reaches=TMReaches(d,c1,one,c2)
    assert same(got_reaches.sequent.right[0],reaches)
    # eel omega w
    got_reaches=eel(got_reaches,omega_w,w)
    got_reaches=cut(got_reaches,Exists(w,omega_w),omega_exists())
    print('phase5: TMReaches done')

    # Discharge + close
    goal_hyps=[trans,func_d,func_tape2,num_one,num_zero,succ_hf,app_c_one,tu_tf,cfg_c1,cfg_c2]
    for hyp in reversed(goal_hyps):
        got_reaches=wl(got_reaches,hyp);imp=Implies(hyp,got_reaches.sequent.right[0])
        left=[f for f in got_reaches.sequent.left if not same(f,hyp)]
        got_reaches=Proof(Sequent(left,[imp]),'implies_right',[got_reaches],principal=imp)
    for v in [c2,c1,tf,tape2,zero,one,hf,c,qH,q2v,d]:
        body=got_reaches.sequent.right[0];fa=Forall(v,body)
        got_reaches=Proof(Sequent(got_reaches.sequent.left,[fa]),'forall_right',[got_reaches],principal=fa,term=v)
    goal=Phase5P()
    got_reaches=cut(ax(goal),goal,got_reaches)
    assert same(got_reaches.sequent.right[0],goal,expand=False),'Phase5P mismatch'
    print('phase5: VERIFIED — proves Phase5P')
    got_reaches.name='phase5'
    return got_reaches


if __name__=='__main__':
    p=phase5()
    from core.zfc import ZFCAxiom
    non=[f for f in p.sequent.left if not isinstance(f,ZFCAxiom)]
    print(f'Left: {len(p.sequent.left)} total, {len(non)} non-ZFC')
