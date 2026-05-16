"""Phase4P proof — single TMStep: (q1,hf,tape2)→(q2,c,tape2). Move left.
Transition: q1,zero→zero,zero(left),q2. Identity tape update. Left move via succ_injection."""
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
    or_intro_left, or_intro_right, or_elim,
    eq_reflexive, eq_symmetric, eq_transitive)
from theorems.sets import (ordpair_exists, ordpair_eq_transfer, ordpair_set_transfer,
    tuple_injection, succ_injection)
from theorems.omega import func_unique_thm, omega_succ_closed
from theorems.tm import (Phase4P, config_decompose, apply_func_transfer,
    config_eq_transfer, tape_update_eq, tmstep_to_reaches)
from theorems.recursion import eq_apply_transfer
from theorems.omega import omega_contains_empty, omega_exists
import core.zfc as zfc


def phase4():
    """ZFC |- Phase4P()"""
    def mk_and(gl, gr):
        L, R = gl.sequent.right[0], gr.sequent.right[0]
        return mp(apply_thm(and_intro(L, R, []), [], L, Implies(R, And(L, R)), gl), gr, R, And(L, R))

    d=Var(postfix='d');q1=Var(postfix='q1');q2=Var(postfix='q2')
    hf=Var(postfix='hf');c=Var(postfix='c');one=Var(postfix='one');zero=Var(postfix='z')
    tape2=Var(postfix='t2');c1=Var(postfix='c1');c2=Var(postfix='c2');w=Var(postfix='w')

    trans=TMTransition(d,q1,zero,zero,zero,q2)
    func_d=FuncDef(d);func_tape2=FuncDef(tape2)
    num_one=Num(one,1);num_zero=Num(zero,0)
    omega_w=Omega(w);in_c_w=In(c,w)
    succ_hf=Successor(hf,c);app_hf_zero=Apply(tape2,hf,zero)
    cfg_c1=TMConfig(c1,q1,hf,tape2);cfg_c2=TMConfig(c2,q2,c,tape2)

    # === Build TMStep(d,c1,c2) ===
    q=Var(postfix='sq');h=Var(postfix='sh');t=Var(postfix='st');sym=Var(postfix='ss')
    w_v=Var(postfix='sw');dir_v=Var(postfix='sd');qn=Var(postfix='sqn')
    hn=Var(postfix='shn');tn=Var(postfix='stn')
    p_cfg=TMConfig(c1,q,h,t);p_read=Apply(t,h,sym)
    p_trans=TMTransition(d,q,sym,w_v,dir_v,qn)
    p_upd=TapeUpdate(tn,t,h,w_v);p_move=HeadMove(h,hn,dir_v)
    p_goal=TMConfig(c2,qn,hn,tn)

    # Step 1: config_decompose → Eq(q,q1), Eq(h,hf), Eq(t,tape2)
    cd=config_decompose()
    eq_q=Eq(q,q1);eq_h=Eq(h,hf);eq_t=Eq(t,tape2)
    and_3eq=And(eq_q,And(eq_h,eq_t))
    got_3eq=apply_thm(cd,[c1,q,h,t,q1,hf,tape2])
    got_3eq=mp(got_3eq,ax(p_cfg),p_cfg,Implies(cfg_c1,and_3eq))
    got_3eq=mp(got_3eq,ax(cfg_c1),cfg_c1,and_3eq)
    got_eq_q=apply_thm(and_elim_left(eq_q,And(eq_h,eq_t),[]),[],and_3eq,eq_q,got_3eq)
    got_eq_ht=apply_thm(and_elim_right(eq_q,And(eq_h,eq_t),[]),[],and_3eq,And(eq_h,eq_t),got_3eq)
    got_eq_h=apply_thm(and_elim_left(eq_h,eq_t,[]),[],And(eq_h,eq_t),eq_h,got_eq_ht)
    got_eq_t=apply_thm(and_elim_right(eq_h,eq_t,[]),[],And(eq_h,eq_t),eq_t,got_eq_ht)

    # Step 2: Eq(sym,zero) via func_unique on tape2
    aft=apply_func_transfer();eat=eq_apply_transfer()
    got_app_th=apply_thm(aft,[t,tape2,h,sym])
    got_app_th=mp(got_app_th,got_eq_t,eq_t,Implies(p_read,Apply(tape2,h,sym)))
    got_app_th=mp(got_app_th,ax(p_read),p_read,Apply(tape2,h,sym))
    got_app_as=apply_thm(eat,[tape2,h,hf,sym])
    got_app_as=mp(got_app_as,got_eq_h,eq_h,Implies(Apply(tape2,h,sym),Apply(tape2,hf,sym)))
    got_app_as=mp(got_app_as,got_app_th,Apply(tape2,h,sym),Apply(tape2,hf,sym))
    fu=func_unique_thm();eq_sym=Eq(sym,zero)
    got_fu=apply_thm(fu,[tape2,hf,sym,zero])
    got_fu=mp(got_fu,ax(func_tape2),func_tape2,got_fu.sequent.right[0].right)
    got_fu=mp(got_fu,got_app_as,Apply(tape2,hf,sym),got_fu.sequent.right[0].right)
    got_eq_sym=mp(got_fu,ax(app_hf_zero),app_hf_zero,eq_sym)
    print('phase4: Eq(sym,zero) done')

    # Step 3: transition decomposition → Eq(w_v,zero), Eq(dir_v,zero), Eq(qn,q2)
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
    # Transfer inp (q,sym)→(q1,zero)
    oet=ordpair_eq_transfer()
    op_inp_q1z=OrdPair(inp,q1,zero)
    got_inp_tr=apply_thm(oet,[q,sym,q1,zero,inp])
    got_inp_tr=mp(got_inp_tr,got_eq_q,eq_q,got_inp_tr.sequent.right[0].right)
    got_inp_tr=mp(got_inp_tr,got_eq_sym,eq_sym,got_inp_tr.sequent.right[0].right)
    got_inp_tr=mp(got_inp_tr,ax(op_inp),op_inp,op_inp_q1z)
    # Known transition with same inp
    dp2=Var(postfix='dp2');out2=Var(postfix='out2')
    op_dp2=OrdPair(dp2,zero,q2);op_out2=OrdPair(out2,zero,dp2)
    got_ex_dp2=apply_thm(oe,[zero,q2],concl=Exists(dp2,op_dp2))
    got_ex_out2=apply_thm(oe,[zero,dp2],concl=Exists(out2,op_out2))
    app_d_out2=Apply(d,inp,out2)
    got_t2=apply_thm(ax(trans),[inp],op_inp_q1z,
        Forall(dp2,Implies(op_dp2,Forall(out2,Implies(op_out2,app_d_out2)))),ax(op_inp_q1z))
    got_t2=apply_thm(got_t2,[dp2],op_dp2,Forall(out2,Implies(op_out2,app_d_out2)),ax(op_dp2))
    got_t2=apply_thm(got_t2,[out2],op_out2,app_d_out2,ax(op_out2))
    got_t2=cut(got_t2,op_inp_q1z,got_inp_tr)
    # func_unique on d → Eq(out1,out2)
    eq_out=Eq(out1,out2)
    got_eq_out=apply_thm(fu,[d,inp,out1,out2])
    got_eq_out=mp(got_eq_out,ax(func_d),func_d,got_eq_out.sequent.right[0].right)
    got_eq_out=mp(got_eq_out,got_t1,app_d_out1,got_eq_out.sequent.right[0].right)
    got_eq_out=mp(got_eq_out,got_t2,app_d_out2,eq_out)
    # tuple_injection
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
    op_dp1_from2=OrdPair(dp1,zero,q2)
    got_dp1f2=mp(apply_thm(ost,[dp1,dp2,zero,q2],eq_dp12,Implies(op_dp2,op_dp1_from2),got_eq_dp),
        ax(op_dp2),op_dp2,op_dp1_from2)
    eq_dir=Eq(dir_v,zero);eq_qn=Eq(qn,q2)
    got_ti_dp=apply_thm(ti,[dir_v,qn,zero,q2,dp1])
    got_ti_dp=mp(got_ti_dp,ax(op_dp1),op_dp1,Implies(op_dp1_from2,And(eq_dir,eq_qn)))
    got_ti_dp=mp(got_ti_dp,got_dp1f2,op_dp1_from2,And(eq_dir,eq_qn))
    got_eq_dir=apply_thm(and_elim_left(eq_dir,eq_qn,[]),[],And(eq_dir,eq_qn),eq_dir,got_ti_dp)
    got_eq_qn=apply_thm(and_elim_right(eq_dir,eq_qn,[]),[],And(eq_dir,eq_qn),eq_qn,got_ti_dp)
    # eel ordpair eigenvars
    def elim(proof,formula,var,ex_proof):
        if any(same(formula,ff) for ff in proof.sequent.left):
            return cut(eel(proof,formula,var),Exists(var,formula),ex_proof)
        return proof
    for var,formula,ex_p in [(out2,op_out2,got_ex_out2),(dp2,op_dp2,got_ex_dp2),
            (out1,op_out1,got_ex_out1),(dp1,op_dp1,got_ex_dp1),(inp,op_inp,got_ex_inp)]:
        got_eq_w=elim(got_eq_w,formula,var,ex_p)
        got_eq_dir=elim(got_eq_dir,formula,var,ex_p)
        got_eq_qn=elim(got_eq_qn,formula,var,ex_p)
    print('phase4: transition decomposed')

    # Step 4: HeadMove left → Eq(hn,c) via succ_injection
    # HeadMove(h,hn,dir_v) with dir_v=zero: right case Succ(h,hn).
    # Transfer Eq(h,hf): Succ(hf,hn). succ_injection(hf,hn,c,w): Succ(hf,hn)∧Succ(hf,c)→In(hn,w)→In(c,w)→Eq(hn,c)
    # But succ_injection needs In(hn,w). Derive from omega_succ_closed: In(c,w)→Succ(hf,c)→In(hf,w).
    # Then Succ(hf,hn)... hmm hn is an eigenvariable inside TMStep. Can't derive In(hn,w) without omega context on hn.
    # Actually succ_injection: ∀s,a,b,w. Succ(s,a)→Succ(s,b)→Omega(w)→In(a,w)→In(b,w)→Eq(a,b)
    # I need In(hn,w) and In(c,w). I have In(c,w). For In(hn,w):
    # From Succ(hf,hn): hf=S(hn). omega_succ_closed reverse? No - omega_succ_closed gives In(k,w)→Succ(sk,k)→In(sk,w).
    # I need: In(hf,w)→Succ(hf,hn)→In(hn,w). That's "predecessor in omega" which we have via omega_transitive:
    # In(hn,hf)∧In(hf,w)→In(hn,w). And In(hn,hf) from Succ(hf,hn): hn∈hf=S(hn)={x:x∈hn∨x=hn}. z=hn: Eq(hn,hn)→In(hn,hf). ✓
    # In(hf,w) from omega_succ_closed: In(c,w)∧Succ(hf,c)→In(hf,w).
    from theorems.sets import omega_transitive as omega_trans_fn
    osc=omega_succ_closed()
    # In(hf,w) from In(c,w)+Succ(hf,c)
    got_hf_w=apply_thm(osc,[w],omega_w,Forall(c,Implies(In(c,w),Forall(hf,Implies(succ_hf,In(hf,w))))),ax(omega_w))
    got_hf_w=apply_thm(got_hf_w,[c],In(c,w),Forall(hf,Implies(succ_hf,In(hf,w))),ax(in_c_w))
    got_hf_w=apply_thm(got_hf_w,[hf],succ_hf,In(hf,w),ax(succ_hf))
    # In(hn,hf) from Succ(hf,hn): instantiate at hn, use Eq(hn,hn)
    # But I don't have Succ(hf,hn) yet — need to derive it from HeadMove.
    # Let me first extract Succ(h,hn) from HeadMove right case, then transfer to Succ(hf,hn).
    # For now, just use succ_injection which needs Succ(hf,hn)+Succ(hf,c)+omega context.
    # Build Succ(hf,hn): from HeadMove right case + transfer.
    # HeadMove = Or(And(Num(dir,1),Succ(hn,h)), And(Num(dir,0),Succ(h,hn)))
    # Right case gives Succ(h,hn). Transfer via Eq(h,hf): Succ(hf,hn).
    # But I'm inside the TMStep ∀ — I have HeadMove(h,hn,dir_v) + Eq(dir_v,zero).
    # The OR elimination for HeadMove:
    #   Left case: And(Num(dir,1),Succ(hn,h)). Num(dir,1)+Eq(dir,zero)+Num(zero,0)→contradiction.
    #   Right case: And(Num(dir,0),Succ(h,hn)). Extract Succ(h,hn). Transfer to Succ(hf,hn) via Eq(h,hf).
    # Then succ_injection.

    # Right case of HeadMove: extract Succ(h,hn), transfer to Succ(hf,hn)
    left_hm=And(Num(dir_v,1),Successor(hn,h))
    right_hm=And(Num(dir_v,0),Successor(h,hn))
    got_shhn=apply_thm(and_elim_right(Num(dir_v,0),Successor(h,hn),[]),[],right_hm,Successor(h,hn),ax(right_hm))
    # Transfer Succ(h,hn) to Succ(hf,hn) via iff_chain: z∈hf↔z∈h↔Or(z∈hn,z=hn)
    from theorems.logic import iff_sym, iff_chain
    from theorems.sets import eq_transfer
    _et=eq_transfer();zv=Var(postfix='_zv')
    iff_hfh=Iff(In(zv,hf),In(zv,h));iff_hh=Iff(In(zv,h),In(zv,hf))
    got_hh=apply_thm(_et,[h,hf,zv]);got_hh=mp(got_hh,ax(eq_h),eq_h,got_hh.sequent.right[0].right)
    got_hfh=apply_thm(iff_sym(In(zv,h),In(zv,hf),[]),[],iff_hh,iff_hfh,got_hh)
    iff_zh=Iff(In(zv,h),Or(In(zv,hn),Eq(zv,hn)))
    got_zh=apply_thm(got_shhn,[zv],concl=iff_zh)
    iff_hf_orn=Iff(In(zv,hf),Or(In(zv,hn),Eq(zv,hn)))
    ic=iff_chain(In(zv,hf),In(zv,h),Or(In(zv,hn),Eq(zv,hn)),[])
    got_hforn=mp(apply_thm(ic,[],iff_hfh,Implies(iff_zh,iff_hf_orn),got_hfh),got_zh,iff_zh,iff_hf_orn)
    succ_hf_hn=Successor(hf,hn)
    fa_hfhn=Forall(zv,iff_hf_orn)
    got_fa_hfhn=Proof(Sequent(got_hforn.sequent.left,[fa_hfhn]),'forall_right',[got_hforn],principal=fa_hfhn,term=zv)
    got_succ_hfhn=cut(ax(succ_hf_hn),succ_hf_hn,got_fa_hfhn)

    # In(hn,hf) from Succ(hf,hn): z∈hf↔Or(z∈hn,z=hn). At z=hn: In(hn,hf)←Eq(hn,hn).
    iff_hn_hf=Iff(In(hn,hf),Or(In(hn,hn),Eq(hn,hn)))
    got_iff_hn=apply_thm(got_succ_hfhn,[hn],concl=iff_hn_hf)
    from theorems.logic import iff_mp_rev
    got_or_hn=apply_thm(or_intro_right(In(hn,hn),Eq(hn,hn),[]),[],Eq(hn,hn),Or(In(hn,hn),Eq(hn,hn)),apply_thm(eq_reflexive(),[hn]))
    got_in_hn_hf=mp(apply_thm(iff_mp_rev(In(hn,hf),Or(In(hn,hn),Eq(hn,hn)),[]),[],
        iff_hn_hf,Implies(Or(In(hn,hn),Eq(hn,hn)),In(hn,hf)),got_iff_hn),
        got_or_hn,Or(In(hn,hn),Eq(hn,hn)),In(hn,hf))
    # In(hn,w) from omega_transitive: In(hn,hf)∧In(hf,w)→In(hn,w)
    _ot=omega_trans_fn()
    got_hn_w=apply_thm(_ot,[w,hf,hn])
    got_hn_w=mp(got_hn_w,ax(omega_w),omega_w,got_hn_w.sequent.right[0].right)
    got_hn_w=mp(got_hn_w,got_hf_w,In(hf,w),got_hn_w.sequent.right[0].right)
    got_hn_w=mp(got_hn_w,got_in_hn_hf,In(hn,hf),In(hn,w))
    # succ_injection: [hf,c,hn,w] → Succ(hf,c),Succ(hf,hn),Omega(w),In(c,w),In(hn,w)→Eq(c,hn)
    _si=succ_injection()
    eq_c_hn=Eq(c,hn)
    got_eq_c_hn=apply_thm(_si,[hf,w,c,hn])
    got_eq_c_hn=mp(got_eq_c_hn,ax(succ_hf),succ_hf,got_eq_c_hn.sequent.right[0].right)
    got_eq_c_hn=mp(got_eq_c_hn,got_succ_hfhn,succ_hf_hn,got_eq_c_hn.sequent.right[0].right)
    got_eq_c_hn=mp(got_eq_c_hn,ax(omega_w),omega_w,got_eq_c_hn.sequent.right[0].right)
    got_eq_c_hn=mp(got_eq_c_hn,ax(in_c_w),in_c_w,got_eq_c_hn.sequent.right[0].right)
    got_eq_c_hn=mp(got_eq_c_hn,got_hn_w,In(hn,w),eq_c_hn)
    eq_hn=Eq(hn,c);_es3=eq_symmetric()
    got_eq_hn=apply_thm(_es3,[c,hn],eq_c_hn,eq_hn,got_eq_c_hn)
    # This is the right case result. For left case: contradiction.
    got_right=got_eq_hn

    # Left case: Num(dir,1)+Eq(dir,zero)→contradiction
    from theorems.tm import zero_neq_one
    got_nd1=apply_thm(and_elim_left(Num(dir_v,1),Successor(hn,h),[]),[],left_hm,Num(dir_v,1),ax(left_hm))
    succ_dz=Successor(dir_v,zero)
    got_sdz=apply_thm(got_nd1,[zero],num_zero,succ_dz,ax(num_zero))
    _zno=zero_neq_one();not_eq_zd=Not(Eq(zero,dir_v))
    got_zno=apply_thm(_zno,[zero,dir_v,zero])
    got_zno=mp(got_zno,ax(num_zero),num_zero,got_zno.sequent.right[0].right)
    got_zno=mp(got_zno,got_sdz,succ_dz,not_eq_zd)
    _es=eq_symmetric();got_ezd=apply_thm(_es,[dir_v,zero],eq_dir,Eq(zero,dir_v),ax(eq_dir))
    gb=Proof(Sequent([Eq(zero,dir_v),not_eq_zd],[]),'not_left',[ax(Eq(zero,dir_v))],principal=not_eq_zd)
    gb=Proof(Sequent(gb.sequent.left,[eq_hn]),'weakening_right',[gb],principal=eq_hn)
    gb=cut(gb,not_eq_zd,got_zno);gb=cut(gb,Eq(zero,dir_v),got_ezd)
    got_left=gb

    # or_elim
    imp_l=Implies(left_hm,eq_hn);ll=[f for f in got_left.sequent.left if not same(f,left_hm)]
    got_il=Proof(Sequent(ll,[imp_l]),'implies_right',[got_left],principal=imp_l)
    imp_r=Implies(right_hm,eq_hn);lr=[f for f in got_right.sequent.left if not same(f,right_hm)]
    got_ir=Proof(Sequent(lr,[imp_r]),'implies_right',[got_right],principal=imp_r)
    oe=or_elim(left_hm,right_hm,eq_hn,[])
    got_eq_hn_final=apply_thm(oe,[],p_move,Implies(imp_l,Implies(imp_r,eq_hn)),ax(p_move))
    got_eq_hn_final=mp(got_eq_hn_final,got_il,imp_l,Implies(imp_r,eq_hn))
    got_eq_hn_final=mp(got_eq_hn_final,got_ir,imp_r,eq_hn)
    print('phase4: Eq(hn,c) done')

    # Step 5: tape_update_eq → Eq(tn,tape2) (identity update: writes zero over zero)
    # tape_update_eq: Function(t)→Apply(t,h,w)→TapeUpdate(tn,t,h,w)→Eq(tn,t)
    _tue=tape_update_eq()
    eq_tn_t=Eq(tn,t)
    got_eq_tn_t=apply_thm(_tue,[tn,tape2,hf,zero])
    got_eq_tn_t=mp(got_eq_tn_t,ax(func_tape2),func_tape2,got_eq_tn_t.sequent.right[0].right)
    # Need Apply(t,h,w_v). We have Apply(tape2,hf,zero)=app_hf_zero. Transfer: Eq(t,tape2),Eq(h,hf),Eq(w_v,zero).
    # Apply(t,h,w_v) ← apply_func_transfer(tape2,t)+eq_apply_transfer(h→hf not needed — wrong direction)
    # Actually: got_app_as already derived Apply(tape2,hf,sym). With Eq(sym,zero): Apply(tape2,hf,zero).
    # But I need Apply(t,h,w_v). Transfer: Eq(t,tape2)→Apply(tape2,...)→Apply(t,...) backwards? No.
    # Simpler: Apply(t,h,w_v). From hypothesis app_hf_zero=Apply(tape2,hf,zero).
    # Use Eq(t,tape2)^-1, Eq(h,hf)^-1, Eq(w_v,zero)^-1 to transfer.
    # Apply(tape2,hf,zero) → Apply(t,hf,zero) via apply_func_transfer(tape2,t)^-1? No, aft goes f→g.
    # Eq(t,tape2): use aft the OTHER way: apply_func_transfer gives Eq(f,g)→Apply(f,x,y)→Apply(g,x,y).
    # I have Eq(t,tape2) and want Apply(t,...). I have Apply(tape2,...). Need Eq(tape2,t)→Apply(tape2,...)→Apply(t,...).
    got_eq_t_sym2=apply_thm(_es,[t,tape2],eq_t,Eq(tape2,t),got_eq_t)
    got_app_t_hf_z=apply_thm(aft,[tape2,t,hf,zero])
    got_app_t_hf_z=mp(got_app_t_hf_z,got_eq_t_sym2,Eq(tape2,t),Implies(Apply(tape2,hf,zero),Apply(t,hf,zero)))
    got_app_t_hf_z=mp(got_app_t_hf_z,ax(app_hf_zero),app_hf_zero,Apply(t,hf,zero))
    # Apply(t,hf,zero) → Apply(t,h,zero) via eq_apply_transfer with Eq(hf,h)
    got_eq_hf_h=apply_thm(_es,[h,hf],eq_h,Eq(hf,h),got_eq_h)
    got_app_t_h_z=apply_thm(eat,[t,hf,h,zero])
    got_app_t_h_z=mp(got_app_t_h_z,got_eq_hf_h,Eq(hf,h),Implies(Apply(t,hf,zero),Apply(t,h,zero)))
    got_app_t_h_z=mp(got_app_t_h_z,got_app_t_hf_z,Apply(t,hf,zero),Apply(t,h,zero))
    # Apply(t,h,zero) → Apply(t,h,w_v) via eq_apply_val_transfer with Eq(zero,w_v)
    from theorems.recursion import eq_apply_val_transfer
    _eavt=eq_apply_val_transfer()
    got_eq_z_wv=apply_thm(_es,[w_v,zero],eq_w_zero,Eq(zero,w_v),got_eq_w)
    got_app_t_h_wv=apply_thm(_eavt,[t,h,zero,w_v])
    got_app_t_h_wv=mp(got_app_t_h_wv,got_eq_z_wv,Eq(zero,w_v),Implies(Apply(t,h,zero),Apply(t,h,w_v)))
    got_app_t_h_wv=mp(got_app_t_h_wv,got_app_t_h_z,Apply(t,h,zero),Apply(t,h,w_v))
    # Now tape_update_eq
    got_eq_tn_t=mp(got_eq_tn_t,got_app_t_h_wv,Apply(t,h,w_v),got_eq_tn_t.sequent.right[0].right)
    got_eq_tn_t=mp(got_eq_tn_t,ax(p_upd),p_upd,eq_tn_t)
    # Eq(tn,t) + Eq(t,tape2) → Eq(tn,tape2)
    _etr=eq_transitive()
    eq_tn=Eq(tn,tape2)
    got_eq_tn=apply_thm(_etr,[tn,t,tape2])
    got_eq_tn=mp(got_eq_tn,got_eq_tn_t,eq_tn_t,Implies(eq_t,eq_tn))
    got_eq_tn=mp(got_eq_tn,got_eq_t,eq_t,eq_tn)
    print('phase4: Eq(tn,tape2) done')

    # Step 6: config_eq_transfer → TMConfig(c2,qn,hn,tn)
    _es2=eq_symmetric
    got_eq_q2_qn=apply_thm(_es(),[qn,q2],eq_qn,Eq(q2,qn),got_eq_qn)
    got_eq_c_hn=apply_thm(_es(),[hn,c],got_eq_hn_final.sequent.right[0],Eq(c,hn),got_eq_hn_final)
    got_eq_t2_tn=apply_thm(_es(),[tn,tape2],eq_tn,Eq(tape2,tn),got_eq_tn)
    cet=config_eq_transfer()
    got_cfg=apply_thm(cet,[c2,q2,c,tape2,qn,hn,tn])
    got_cfg=mp(got_cfg,ax(cfg_c2),cfg_c2,got_cfg.sequent.right[0].right)
    got_cfg=mp(got_cfg,got_eq_q2_qn,Eq(q2,qn),got_cfg.sequent.right[0].right)
    got_cfg=mp(got_cfg,got_eq_c_hn,Eq(c,hn),got_cfg.sequent.right[0].right)
    got_cfg=mp(got_cfg,got_eq_t2_tn,Eq(tape2,tn),p_goal)
    print('phase4: TMConfig(c2,...) done')

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
    print('phase4: TMStep done')

    # TMStep → TMReaches via tmstep_to_reaches
    succ_one_z=Successor(one,zero)
    got_succ_oz=apply_thm(ax(num_one),[zero],num_zero,succ_one_z,ax(num_zero))
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
    print('phase4: TMReaches done')

    # Discharge + ∀-close
    goal_hyps=[trans,func_d,func_tape2,num_one,num_zero,omega_w,in_c_w,succ_hf,app_hf_zero,cfg_c1,cfg_c2]
    for hyp in reversed(goal_hyps):
        got_reaches=wl(got_reaches,hyp);imp=Implies(hyp,got_reaches.sequent.right[0])
        left=[f for f in got_reaches.sequent.left if not same(f,hyp)]
        got_reaches=Proof(Sequent(left,[imp]),'implies_right',[got_reaches],principal=imp)
    for v in [w,c2,c1,tape2,zero,one,c,hf,q2,q1,d]:
        body=got_reaches.sequent.right[0];fa=Forall(v,body)
        got_reaches=Proof(Sequent(got_reaches.sequent.left,[fa]),'forall_right',[got_reaches],principal=fa,term=v)
    goal=Phase4P()
    got_reaches=cut(ax(goal),goal,got_reaches)
    assert same(got_reaches.sequent.right[0],goal,expand=False),'Phase4P mismatch'
    print('phase4: VERIFIED — proves Phase4P')
    got_reaches.name='phase4'
    return got_reaches


if __name__=='__main__':
    p=phase4()
    from core.zfc import ZFCAxiom
    non=[f for f in p.sequent.left if not isinstance(f,ZFCAxiom)]
    print(f'Left: {len(p.sequent.left)} total, {len(non)} non-ZFC')
