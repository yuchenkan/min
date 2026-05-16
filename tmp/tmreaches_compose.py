"""TMReachesCompose: chain two TMReaches via omega induction on b.

Q(j) = ∃pos_j,cj. Plus(a,j,pos_j) ∧ Apply(tr2,j,cj) ∧ TMReaches(d,x,pos_j,cj)
Uses phase1_step_extend_trace at each step.
"""
import sys; sys.path.insert(0, '/root/min/src')
from core.lang import Var, In, Not, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq
from core.proof import Proof, Sequent, same, _var_free_in_sequent, _subst
from vocab.ordpair import OrdPair, Successor
from vocab.omega import Omega, Num
from vocab.sets import Empty, TransitiveSet
from vocab.tm import TMConfig, TMTransition, TMStep, TMReaches
from vocab.functions import Function as FuncDef, Apply
from vocab.recursion import Plus as PlusDef
from tactics import apply_thm, mp, ax, fl, eir, eel, cut, wl, wr, weaken_to
from theorems.logic import (and_intro, and_elim_left, and_elim_right,
    or_intro_left, or_intro_right, or_elim,
    eq_reflexive, eq_symmetric, iff_mp, iff_mp_rev, unique_empty, eq_substitution)
from theorems.sets import (eq_transfer, ordpair_exists, singleton_exists,
    omega_transitive_set as ots_fn, successor_exists)
from theorems.omega import (omega_smallest_inductive, omega_contains_empty,
    omega_succ_closed, func_unique_thm)
from theorems.arithmetic import plus_zero_exists, plus_succ_right, plus_val_in_omega
from theorems.recursion import eq_apply_transfer, eq_apply_val_transfer
from theorems.tm import (TMReachesCompose, phase1_step_extend_trace)
import core.zfc as zfc


def tmreaches_compose():
    """ZFC |- TMReachesCompose()"""
    def mk_and(gl,gr):
        L,R=gl.sequent.right[0],gr.sequent.right[0]
        return mp(apply_thm(and_intro(L,R,[]),[],L,Implies(R,And(L,R)),gl),gr,R,And(L,R))

    d=Var(postfix='d');x=Var(postfix='x');y=Var(postfix='y');zv=Var(postfix='zv')
    a=Var(postfix='a');b=Var(postfix='b');nv=Var(postfix='nv');w=Var(postfix='w')
    omega_w=Omega(w);in_a_w=In(a,w);in_b_w=In(b,w)
    reaches1=TMReaches(d,x,a,y);reaches2=TMReaches(d,y,b,zv)
    plus_abn=PlusDef(a,b,nv)

    # Open TMReaches2: ∃tr2. And(Func, And(db, And(base, And(step, reached))))
    r2_exp=reaches2.expand();tr2=r2_exp.var;r2_body=r2_exp.body
    r2_func=r2_body.left
    r2_r1=r2_body.right;r2_db=r2_r1.left
    r2_r2=r2_r1.right;r2_base=r2_r2.left
    r2_r3=r2_r2.right;r2_step=r2_r3.left;r2_reached=r2_r3.right

    # Q_inner(j) = ∃pos_j,cj. Plus(a,j,pos_j) ∧ Apply(tr2,j,cj) ∧ TMReaches(d,x,pos_j,cj)
    # Q(j) = Or(In(j,b),Eq(j,b)) → Q_inner(j)  [guarded, like phase1/phase3]
    pos_j=Var(postfix='pj');cj=Var(postfix='cj')
    def Q_inner(jj):
        return Exists(pos_j, Exists(cj, And(PlusDef(a,jj,pos_j),
            And(Apply(tr2,jj,cj), TMReaches(d,x,pos_j,cj)))))
    def Q(jj):
        return Implies(Or(In(jj,b),Eq(jj,b)), Q_inner(jj))

    # Separation
    pv=Var(postfix='ind_pv');xv=Var(postfix='ind_xv')
    sep=zfc.Separation(Q,[a,b,d,x,tr2,pos_j,cj])
    sep_ax=Proof(Sequent([sep],[sep]),'axiom',principal=sep)
    char_pv=Forall(xv,Iff(In(xv,pv),And(In(xv,w),Q(xv))))
    got_ex_pv=apply_thm(sep_ax,[cj,pos_j,tr2,x,d,b,a,w],concl=Exists(pv,char_pv))
    def char_bwd(term,got_in_w,got_Q):
        gi=apply_thm(ax(char_pv),[term]);ii=gi.sequent.right[0];af=ii.right
        gr=apply_thm(iff_mp_rev(ii.left,ii.right,[]),[],ii,Implies(af,ii.left),gi)
        ai2=and_intro(af.left,af.right,[]);ga=apply_thm(ai2,[],af.left,Implies(af.right,af),got_in_w)
        gand=mp(ga,got_Q,af.right,af);return mp(gr,gand,af,ii.left)
    def char_fwd(term):
        gi=apply_thm(ax(char_pv),[term]);ii=gi.sequent.right[0]
        gimp=apply_thm(iff_mp(ii.left,ii.right,[]),[],ii,Implies(ii.left,ii.right),gi)
        return mp(gimp,ax(In(term,pv)),In(term,pv),ii.right)
    print('compose: sep done')

    # === BASE ===
    z=Var(postfix='z');num_z=Num(z,0)
    oce=omega_contains_empty()
    got_z_w=apply_thm(oce,[w],omega_w,Forall(z,Implies(num_z,In(z,w))),ax(omega_w))
    got_z_w=apply_thm(got_z_w,[z],num_z,In(z,w),ax(num_z))
    _pze=plus_zero_exists()
    got_plus_az=apply_thm(_pze,[w,a,z])
    got_plus_az=mp(got_plus_az,ax(omega_w),omega_w,got_plus_az.sequent.right[0].right)
    got_plus_az=mp(got_plus_az,ax(in_a_w),in_a_w,got_plus_az.sequent.right[0].right)
    got_plus_az=mp(got_plus_az,ax(num_z),num_z,got_plus_az.sequent.right[0].right)
    # Apply(tr2,z,y) from r2_base
    got_app_z_y=apply_thm(ax(r2_base),[z]);cur=got_app_z_y.sequent.right[0]
    got_app_z_y=mp(got_app_z_y,ax(num_z),cur.left,cur.right)
    # Assemble Q(z)
    qi_z=Q_inner(z)
    got_q=mk_and(got_app_z_y,ax(reaches1))
    got_q=mk_and(got_plus_az,got_q)
    qi_z_pos=qi_z.var;qi_z_inner=qi_z.body;qi_z_cj=qi_z_inner.var;qi_z_body=qi_z_inner.body
    body_cj=_subst(qi_z_body,qi_z_pos,a)
    got_ecj=eir(got_q,body_cj,qi_z_cj,y)
    got_epos=eir(got_ecj,qi_z_inner,qi_z_pos,a)
    assert same(got_epos.sequent.right[0],qi_z),'Q_inner(z) mismatch'
    # Q(z) = Or(In(z,b),Eq(z,b)) → Q_inner(z). Weaken with guard.
    or_zb=Or(In(z,b),Eq(z,b))
    got_Qz=wl(got_epos,or_zb);imp_qz=Implies(or_zb,got_Qz.sequent.right[0])
    lqz=[f for f in got_Qz.sequent.left if not same(f,or_zb)]
    got_Qz=Proof(Sequent(lqz,[imp_qz]),'implies_right',[got_Qz],principal=imp_qz)
    got_base_pv=char_bwd(z,got_z_w,got_Qz)
    # Inductive base
    zero_v=Var(postfix='ind_zero');ue=unique_empty();es_thm=eq_substitution()
    got_eq=apply_thm(ue,[zero_v],Empty(zero_v),Forall(z,Implies(num_z,Eq(zero_v,z))),ax(Empty(zero_v)))
    got_eq=apply_thm(got_eq,[z],num_z,Eq(zero_v,z),ax(num_z))
    iff_zv=Iff(In(zero_v,pv),In(z,pv))
    got_iff=apply_thm(es_thm,[zero_v,z,pv],Eq(zero_v,z),iff_zv,got_eq)
    got_zv_pv=mp(apply_thm(iff_mp_rev(In(zero_v,pv),In(z,pv),[]),[],iff_zv,Implies(In(z,pv),In(zero_v,pv)),got_iff),
        got_base_pv,In(z,pv),In(zero_v,pv))
    imp_ez=Implies(Empty(zero_v),In(zero_v,pv))
    lez=[f for f in got_zv_pv.sequent.left if not same(f,Empty(zero_v))]
    got_ind_base=Proof(Sequent(lez,[imp_ez]),'implies_right',[got_zv_pv],principal=imp_ez)
    got_ind_base=Proof(Sequent(got_ind_base.sequent.left,[Forall(zero_v,imp_ez)]),'forall_right',[got_ind_base],principal=Forall(zero_v,imp_ez),term=zero_v)
    print('compose: base done')

    # === STEP ===
    n=Var(postfix='ind_n');sn=Var(postfix='ind_sn');succ_sn=Successor(sn,n)
    got_an=char_fwd(n)
    got_in_nw=apply_thm(and_elim_left(In(n,w),Q(n),[]),[],got_an.sequent.right[0],In(n,w),got_an)
    got_Qn_guard=apply_thm(and_elim_right(In(n,w),Q(n),[]),[],got_an.sequent.right[0],Q(n),got_an)
    osc=omega_succ_closed()
    got_snw=apply_thm(osc,[w],omega_w,Forall(n,Implies(In(n,w),Forall(sn,Implies(succ_sn,In(sn,w))))),ax(omega_w))
    got_snw=apply_thm(got_snw,[n],In(n,w),Forall(sn,Implies(succ_sn,In(sn,w))),got_in_nw)
    got_snw=apply_thm(got_snw,[sn],succ_sn,In(sn,w),ax(succ_sn))
    # In(n,b) from Or(In(sn,b),Eq(sn,b))
    or_snb=Or(In(sn,b),Eq(sn,b))
    or_nsn=Or(In(n,n),Eq(n,n));iff_nsn=Iff(In(n,sn),or_nsn)
    got_insn=apply_thm(ax(succ_sn),[n],concl=iff_nsn)
    got_orn=apply_thm(or_intro_right(In(n,n),Eq(n,n),[]),[],Eq(n,n),or_nsn,apply_thm(eq_reflexive(),[n]))
    got_insn=mp(apply_thm(iff_mp_rev(In(n,sn),or_nsn,[]),[],iff_nsn,Implies(or_nsn,In(n,sn)),got_insn),got_orn,or_nsn,In(n,sn))
    _ots=ots_fn();gta=apply_thm(_ots,[w,b]);gta=mp(gta,ax(omega_w),omega_w,gta.sequent.right[0].right)
    gta=mp(gta,ax(in_b_w),in_b_w,TransitiveSet(b))
    gc1=apply_thm(gta,[sn]);cur=gc1.sequent.right[0];gc1=mp(gc1,ax(In(sn,b)),cur.left,cur.right)
    gc1=apply_thm(gc1,[n]);cur=gc1.sequent.right[0];gc1=mp(gc1,got_insn,cur.left,cur.right)
    _et=eq_transfer();gis=apply_thm(_et,[sn,b,n]);gis=mp(gis,ax(Eq(sn,b)),Eq(sn,b),gis.sequent.right[0].right)
    gc2=mp(apply_thm(iff_mp(In(n,sn),In(n,b),[]),[],Iff(In(n,sn),In(n,b)),Implies(In(n,sn),In(n,b)),gis),got_insn,In(n,sn),In(n,b))
    ic1=Implies(In(sn,b),In(n,b));lc1=[f for f in gc1.sequent.left if not same(f,In(sn,b))]
    gic1=Proof(Sequent(lc1,[ic1]),'implies_right',[gc1],principal=ic1)
    ic2=Implies(Eq(sn,b),In(n,b));lc2=[f for f in gc2.sequent.left if not same(f,Eq(sn,b))]
    gic2=Proof(Sequent(lc2,[ic2]),'implies_right',[gc2],principal=ic2)
    oena=or_elim(In(sn,b),Eq(sn,b),In(n,b),[])
    got_inb=apply_thm(oena,[],or_snb,Implies(ic1,Implies(ic2,In(n,b))),ax(or_snb))
    got_inb=mp(got_inb,gic1,ic1,Implies(ic2,In(n,b)));got_inb=mp(got_inb,gic2,ic2,In(n,b))
    or_nb=Or(In(n,b),Eq(n,b))
    got_ornb=apply_thm(or_intro_left(In(n,b),Eq(n,b),[]),[],In(n,b),or_nb,got_inb)
    # Now extract Q_inner(n) from guarded Q(n) + Or(In(n,b),Eq(n,b))
    got_Qn_val=mp(got_Qn_guard,got_ornb,or_nb,Q_inner(n))
    got_Q2n=got_Qn_val
    # Open Q(n)
    qn=Q_inner(n);qn_pos=qn.var;qn_inner=qn.body;qn_cj=qn_inner.var;qn_body=qn_inner.body
    got_plus_n=apply_thm(and_elim_left(qn_body.left,qn_body.right,[]),[],qn_body,qn_body.left,ax(qn_body))
    got_rest_n=apply_thm(and_elim_right(qn_body.left,qn_body.right,[]),[],qn_body,qn_body.right,ax(qn_body))
    got_app_n=apply_thm(and_elim_left(qn_body.right.left,qn_body.right.right,[]),[],qn_body.right,qn_body.right.left,got_rest_n)
    got_reaches_n=apply_thm(and_elim_right(qn_body.right.left,qn_body.right.right,[]),[],qn_body.right,qn_body.right.right,got_rest_n)
    # Open TMReaches(d,x,pos_j,cj): get trace with Function+dom_bound+base+step+reached
    rn=got_reaches_n.sequent.right[0];rn_exp=rn.expand();rn_tra=rn_exp.var;rn_body=rn_exp.body
    rn_func=rn_body.left;rn_r1=rn_body.right;rn_db=rn_r1.left
    rn_r2=rn_r1.right;rn_base=rn_r2.left;rn_r3=rn_r2.right;rn_step=rn_r3.left;rn_reached=rn_r3.right
    got_rn_func=apply_thm(and_elim_left(rn_func,rn_r1,[]),[],rn_body,rn_func,ax(rn_body))
    got_rn_r1=apply_thm(and_elim_right(rn_func,rn_r1,[]),[],rn_body,rn_r1,ax(rn_body))
    got_rn_db=apply_thm(and_elim_left(rn_db,rn_r2,[]),[],rn_r1,rn_db,got_rn_r1)
    got_rn_r2=apply_thm(and_elim_right(rn_db,rn_r2,[]),[],rn_r1,rn_r2,got_rn_r1)
    got_rn_base=apply_thm(and_elim_left(rn_base,rn_r3,[]),[],rn_r2,rn_base,got_rn_r2)
    got_rn_r3=apply_thm(and_elim_right(rn_base,rn_r3,[]),[],rn_r2,rn_r3,got_rn_r2)
    got_rn_step=apply_thm(and_elim_left(rn_step,rn_reached,[]),[],rn_r3,rn_step,got_rn_r3)
    got_rn_reached=apply_thm(and_elim_right(rn_step,rn_reached,[]),[],rn_r3,rn_reached,got_rn_r3)
    print('compose step: Q(n) + TMReaches decomposed')

    # step2 at n: ∃ck1. And(Apply(tr2,sn,ck1), TMStep(d,cj,ck1))
    got_step2=apply_thm(ax(r2_step),[n]);cur=got_step2.sequent.right[0]
    got_step2=mp(got_step2,got_inb,cur.left,cur.right)
    got_step2=apply_thm(got_step2,[sn]);cur=got_step2.sequent.right[0]
    got_step2=mp(got_step2,ax(succ_sn),cur.left,cur.right)
    got_step2=apply_thm(got_step2,[qn_cj]);cur=got_step2.sequent.right[0]
    got_step2=mp(got_step2,got_app_n,cur.left,cur.right)
    ck1_ex=got_step2.sequent.right[0];ck1_var=ck1_ex.var;ck1_body=ck1_ex.body
    got_app_sn=apply_thm(and_elim_left(ck1_body.left,ck1_body.right,[]),[],ck1_body,ck1_body.left,ax(ck1_body))
    got_tmstep=apply_thm(and_elim_right(ck1_body.left,ck1_body.right,[]),[],ck1_body,ck1_body.right,ax(ck1_body))

    # func_unique on rn_tra: Apply(rn_tra,pos_j,cj_n)=rn_reached and Apply(rn_tra,pos_j,qn_cj)→Eq(cj_n,qn_cj)
    # Actually rn_reached IS Apply(rn_tra,qn_pos,qn_cj) — the reached component.
    # TMStep(d,qn_cj,ck1) from step2. We have it directly. ✓

    # Successor(spos, qn_pos) for new position
    spos=Var(postfix='spos');succ_spos=Successor(spos,qn_pos)
    got_ex_spos=apply_thm(successor_exists(),[qn_pos],concl=Exists(spos,succ_spos))

    # In(qn_pos,w) from plus_val_in_omega
    _pvi=plus_val_in_omega()
    got_pos_w=apply_thm(_pvi,[w,a,n,qn_pos])
    got_pos_w=mp(got_pos_w,ax(omega_w),omega_w,got_pos_w.sequent.right[0].right)
    got_pos_w=mp(got_pos_w,ax(in_a_w),in_a_w,got_pos_w.sequent.right[0].right)
    got_pos_w=mp(got_pos_w,got_in_nw,In(n,w),got_pos_w.sequent.right[0].right)
    got_pos_w=mp(got_pos_w,got_plus_n,qn_body.left,In(qn_pos,w))

    # phase1_step_extend_trace: extend the trace by one step
    _pet=phase1_step_extend_trace()
    got_ext=apply_thm(_pet,[rn_tra,spos,ck1_var,x,qn_pos,d,qn_cj,w])
    got_ext=mp(got_ext,got_rn_func,rn_func,got_ext.sequent.right[0].right)
    got_ext=mp(got_ext,got_rn_db,rn_db,got_ext.sequent.right[0].right)
    got_ext=mp(got_ext,ax(omega_w),omega_w,got_ext.sequent.right[0].right)
    got_ext=mp(got_ext,got_pos_w,In(qn_pos,w),got_ext.sequent.right[0].right)
    got_ext=mp(got_ext,ax(succ_spos),succ_spos,got_ext.sequent.right[0].right)
    got_ext=mp(got_ext,got_rn_base,rn_base,got_ext.sequent.right[0].right)
    got_ext=mp(got_ext,got_rn_step,rn_step,got_ext.sequent.right[0].right)
    got_ext=mp(got_ext,got_tmstep,got_tmstep.sequent.right[0],got_ext.sequent.right[0].right)
    got_ext=mp(got_ext,got_rn_reached,rn_reached,got_ext.sequent.right[0].right)
    # ∃trn. And(Function(trn), And(dom_bound(trn,spos), And(base(trn,x), And(Apply(trn,spos,ck1), step_valid(trn,spos)))))
    print('compose step: extend_trace done')

    # Build TMReaches(d,x,spos,ck1) from the extended trace
    extx=got_ext.sequent.right[0];trn=extx.var;extb=extx.body
    e0=extb
    g_func=apply_thm(and_elim_left(e0.left,e0.right,[]),[],e0,e0.left,ax(e0))
    e1=e0.right;ge1=apply_thm(and_elim_right(e0.left,e1,[]),[],e0,e1,ax(e0))
    g_db=apply_thm(and_elim_left(e1.left,e1.right,[]),[],e1,e1.left,ge1)
    e2=e1.right;ge2=apply_thm(and_elim_right(e1.left,e2,[]),[],e1,e2,ge1)
    g_bc=apply_thm(and_elim_left(e2.left,e2.right,[]),[],e2,e2.left,ge2)
    e3=e2.right;ge3=apply_thm(and_elim_right(e2.left,e3,[]),[],e2,e3,ge2)
    g_app=apply_thm(and_elim_left(e3.left,e3.right,[]),[],e3,e3.left,ge3)
    g_sv=apply_thm(and_elim_right(e3.left,e3.right,[]),[],e3,e3.right,ge3)
    reaches_new=TMReaches(d,x,spos,ck1_var)
    rn_exp2=reaches_new.expand();rn_tra2=rn_exp2.var;rn_body2=rn_exp2.body
    r_and=mk_and(g_sv,g_app);r_and=mk_and(g_bc,r_and);r_and=mk_and(g_db,r_and);r_and=mk_and(g_func,r_and)
    got_reaches_new=eir(r_and,rn_body2,rn_tra2,trn)
    got_reaches_new=cut(ax(reaches_new),reaches_new,got_reaches_new)

    # Plus(a,sn,spos) from plus_succ_right
    _psr=plus_succ_right()
    got_plus_sn=apply_thm(_psr,[w,a,n,qn_pos,sn,spos])
    got_plus_sn=mp(got_plus_sn,ax(omega_w),omega_w,got_plus_sn.sequent.right[0].right)
    got_plus_sn=mp(got_plus_sn,ax(in_a_w),in_a_w,got_plus_sn.sequent.right[0].right)
    got_plus_sn=mp(got_plus_sn,got_in_nw,In(n,w),got_plus_sn.sequent.right[0].right)
    got_plus_sn=mp(got_plus_sn,got_plus_n,qn_body.left,got_plus_sn.sequent.right[0].right)
    got_plus_sn=mp(got_plus_sn,ax(succ_sn),succ_sn,got_plus_sn.sequent.right[0].right)
    got_plus_sn=mp(got_plus_sn,ax(succ_spos),succ_spos,got_plus_sn.sequent.right[0].right)
    print('compose step: Plus(a,sn,spos) done')

    # Assemble Q(sn) = ∃pos_j,cj. And(Plus(a,sn,pos_j), And(Apply(tr2,sn,cj), TMReaches(d,x,pos_j,cj)))
    qi_sn=Q_inner(sn)
    got_qsn_and=mk_and(got_app_sn,got_reaches_new)
    got_qsn_and=mk_and(got_plus_sn,got_qsn_and)
    qisn_pos=qi_sn.var;qisn_inner=qi_sn.body;qisn_cj=qisn_inner.var;qisn_body=qisn_inner.body
    body_cj2=_subst(qisn_body,qisn_pos,spos)
    got_ecj2=eir(got_qsn_and,body_cj2,qisn_cj,ck1_var)
    got_epos2=eir(got_ecj2,qisn_inner,qisn_pos,spos)
    assert same(got_epos2.sequent.right[0],qi_sn),'Q_inner(sn) mismatch'
    print('compose step: Q(sn) assembled')

    # eel eigenvars: trn from extb, ck1 from ck1_body, spos from succ_spos,
    # rn_tra from rn_body, qn_cj from qn_inner.body, qn_pos from qn.body
    got_epos2=eel(got_epos2,extb,trn);got_epos2=cut(got_epos2,extx,got_ext)
    got_epos2=eel(got_epos2,succ_spos,spos);got_epos2=cut(got_epos2,Exists(spos,succ_spos),got_ex_spos)
    got_epos2=eel(got_epos2,ck1_body,ck1_var);got_epos2=cut(got_epos2,ck1_ex,got_step2)
    got_epos2=eel(got_epos2,rn_body,rn_tra);got_epos2=cut(got_epos2,rn_exp,got_reaches_n)
    got_epos2=eel(got_epos2,qn_body,qn_cj);got_epos2=cut(got_epos2,qn_inner,ax(qn_inner))
    got_epos2=eel(got_epos2,qn_inner,qn_pos);got_epos2=cut(got_epos2,Q_inner(n),got_Q2n)
    print('compose step: eigenvars cleaned')

    # Q(sn) proved. In(sn,pv):
    # Q(sn) = Or(In(sn,b),Eq(sn,b)) → Q_inner(sn). Weaken with guard.
    imp_qsn=Implies(or_snb,got_epos2.sequent.right[0])
    lqsn=[f for f in wl(got_epos2,or_snb).sequent.left if not same(f,or_snb)]
    got_Qsn=Proof(Sequent(lqsn,[imp_qsn]),'implies_right',[wl(got_epos2,or_snb)],principal=imp_qsn)
    got_step_pv=char_bwd(sn,got_snw,got_Qsn)
    if any(same(In(n,w),f) for f in got_step_pv.sequent.left):
        got_step_pv=cut(got_step_pv,In(n,w),got_in_nw)
    print('compose step: In(sn,pv) done')

    # Discharge sn, n
    proof=got_step_pv
    for ff in list(proof.sequent.left):
        if _var_free_in_sequent(sn,Sequent([ff],[])) and not same(ff,succ_sn):
            proof=wl(proof,ff);imp=Implies(ff,proof.sequent.right[0])
            left=[f for f in proof.sequent.left if not same(f,ff)];proof=Proof(Sequent(left,[imp]),'implies_right',[proof],principal=imp)
    imp_sn=Implies(succ_sn,proof.sequent.right[0]);left_sn=[f for f in proof.sequent.left if not same(f,succ_sn)]
    proof=Proof(Sequent(left_sn,[imp_sn]),'implies_right',[proof],principal=imp_sn)
    proof=Proof(Sequent(proof.sequent.left,[Forall(sn,imp_sn)]),'forall_right',[proof],principal=Forall(sn,imp_sn),term=sn)
    for ff in list(proof.sequent.left):
        if _var_free_in_sequent(n,Sequent([ff],[])) and not same(ff,In(n,pv)):
            proof=wl(proof,ff);imp=Implies(ff,proof.sequent.right[0])
            left=[f for f in proof.sequent.left if not same(f,ff)];proof=Proof(Sequent(left,[imp]),'implies_right',[proof],principal=imp)
    imp_npv=Implies(In(n,pv),proof.sequent.right[0]);left_npv=[f for f in proof.sequent.left if not same(f,In(n,pv))]
    got_ind_step=Proof(Sequent(left_npv,[imp_npv]),'implies_right',[proof],principal=imp_npv)
    got_ind_step=Proof(Sequent(got_ind_step.sequent.left,[Forall(n,imp_npv)]),'forall_right',[got_ind_step],principal=Forall(n,imp_npv),term=n)
    print('compose: ind_step done')

    # === OSI ===
    all_ctx=list(got_ind_base.sequent.left)
    for f_ in got_ind_step.sequent.left:
        if not any(same(f_,g) for g in all_ctx):all_ctx.append(f_)
    gib_w=weaken_to(got_ind_base,all_ctx);gis_w=weaken_to(got_ind_step,all_ctx)
    ibf=gib_w.sequent.right[0];isf=gis_w.sequent.right[0];ai=And(ibf,isf)
    got_ind=mp(apply_thm(and_intro(ibf,isf,[]),[],ibf,Implies(isf,ai),gib_w),gis_w,isf,ai)
    xs2=Var(postfix='xs2');got_fwd=char_fwd(xs2);inxw=got_fwd.sequent.right[0].left
    got_xw=apply_thm(and_elim_left(inxw,got_fwd.sequent.right[0].right,[]),[],got_fwd.sequent.right[0],inxw,got_fwd)
    imp_sub=Implies(In(xs2,pv),inxw);ls=[f for f in got_xw.sequent.left if not same(f,In(xs2,pv))]
    got_sub=Proof(Sequent(ls,[imp_sub]),'implies_right',[got_xw],principal=imp_sub)
    spw=Forall(xs2,imp_sub);got_sub=Proof(Sequent(got_sub.sequent.left,[spw]),'forall_right',[got_sub],principal=spw,term=xs2)
    osi=omega_smallest_inductive();eq_pw=Eq(pv,w)
    got_osi=apply_thm(osi,[pv,w])
    while not same(got_osi.sequent.right[0],eq_pw):
        cur=got_osi.sequent.right[0];got_osi=mp(got_osi,ax(cur.left),cur.left,cur.right)
    all_osi=list(all_ctx)
    for f_ in got_sub.sequent.left:
        if not any(same(f_,g) for g in all_osi):all_osi.append(f_)
    gsw=weaken_to(got_sub,all_osi);giw=weaken_to(got_ind,all_osi)
    gas=mp(apply_thm(and_intro(spw,ai,[]),[],spw,Implies(ai,And(spw,ai)),gsw),giw,ai,And(spw,ai))
    # Cut osi's hypothesis: And(Subset(pv,w), Inductive(pv))
    from vocab import Subset as SubsetV, Inductive as InductiveV
    target_si = And(SubsetV(pv,w), InductiveV(pv))
    # Build target_si from got_sub (Subset expansion) + got_ind (Inductive expansion)
    got_target = mk_and(gsw, giw)
    # Wrap as vocab: cut ax(target_si) with got_target
    # Just cut the non-axiom directly with got_target (no vocab wrapping)
    non_ax=[f_ for f_ in got_osi.sequent.left if not isinstance(f_,zfc.ZFCAxiom) and not same(f_,omega_w)]
    for h in non_ax:
        print(f'  h: {str(h)}')
        print(f'  got_target.right: {str(got_target.sequent.right[0])}')
        print(f'  same? {same(h, got_target.sequent.right[0])}')
        got_osi=cut(got_osi,h,got_target)
    print('compose: osi done')

    # === Extract Q(b) → TMReaches(d,x,nv,zv) ===
    iff_bpv=Iff(In(b,pv),In(b,w))
    got_iff_b=cut(fl(eq_pw,iff_bpv,b),eq_pw,got_osi)
    got_bpv=mp(apply_thm(iff_mp_rev(In(b,pv),In(b,w),[]),[],iff_bpv,Implies(In(b,w),In(b,pv)),got_iff_b),ax(in_b_w),in_b_w,In(b,pv))
    got_andb=cut(char_fwd(b),In(b,pv),got_bpv)
    got_Qb=apply_thm(and_elim_right(In(b,w),Q(b),[]),[],got_andb.sequent.right[0],Q(b),got_andb)
    or_bb=Or(In(b,b),Eq(b,b));got_orbb=apply_thm(or_intro_right(In(b,b),Eq(b,b),[]),[],Eq(b,b),or_bb,apply_thm(eq_reflexive(),[b]))
    got_Qb_val=mp(got_Qb,got_orbb,or_bb,Q_inner(b))
    got_Qb_val=eel(got_Qb_val,char_pv,pv);got_Qb_val=cut(got_Qb_val,Exists(pv,char_pv),got_ex_pv)
    # Q(b) = ∃pos_b,cb. Plus(a,b,pos_b) ∧ Apply(tr2,b,cb) ∧ TMReaches(d,x,pos_b,cb)
    # From Plus(a,b,nv) [hypothesis] + plus_val_unique → pos_b=nv.
    # From Apply(tr2,b,zv)=r2_reached + func_unique(tr2) → cb=zv.
    # Then TMReaches(d,x,nv,zv).
    qib=Q_inner(b);qb_pos=qib.var;qb_inner=qib.body;qb_cj=qb_inner.var;qb_body=qb_inner.body
    got_qb_plus=apply_thm(and_elim_left(qb_body.left,qb_body.right,[]),[],qb_body,qb_body.left,ax(qb_body))
    got_qb_rest=apply_thm(and_elim_right(qb_body.left,qb_body.right,[]),[],qb_body,qb_body.right,ax(qb_body))
    got_qb_app=apply_thm(and_elim_left(qb_body.right.left,qb_body.right.right,[]),[],qb_body.right,qb_body.right.left,got_qb_rest)
    got_qb_reaches=apply_thm(and_elim_right(qb_body.right.left,qb_body.right.right,[]),[],qb_body.right,qb_body.right.right,got_qb_rest)
    # pos_b=nv: plus_val_unique
    from theorems.arithmetic import plus_val_unique
    _pvu=plus_val_unique()
    got_eq_pos=apply_thm(_pvu,[w,a,b,qb_pos,nv])
    got_eq_pos=mp(got_eq_pos,ax(omega_w),omega_w,got_eq_pos.sequent.right[0].right)
    got_eq_pos=mp(got_eq_pos,ax(in_a_w),in_a_w,got_eq_pos.sequent.right[0].right)
    got_eq_pos=mp(got_eq_pos,ax(in_b_w),in_b_w,got_eq_pos.sequent.right[0].right)
    got_eq_pos=mp(got_eq_pos,got_qb_plus,qb_body.left,got_eq_pos.sequent.right[0].right)
    got_eq_pos=mp(got_eq_pos,ax(plus_abn),plus_abn,Eq(qb_pos,nv))
    # cb=zv: func_unique(tr2) + Apply(tr2,b,cb) + Apply(tr2,b,zv)=r2_reached
    _fu=func_unique_thm()
    got_eq_cb=apply_thm(_fu,[tr2,b,qb_cj,zv])
    got_eq_cb=mp(got_eq_cb,ax(r2_func),r2_func,got_eq_cb.sequent.right[0].right)
    got_eq_cb=mp(got_eq_cb,got_qb_app,qb_body.right.left,got_eq_cb.sequent.right[0].right)
    got_eq_cb=mp(got_eq_cb,ax(r2_reached),r2_reached,Eq(qb_cj,zv))
    # Transfer TMReaches(d,x,pos_b,cb) → TMReaches(d,x,nv,zv)
    # TMReaches.subst(pos_b,nv).subst(cb,zv) = TMReaches(d,x,nv,zv). Need eq-based transfer.
    # Actually TMReaches is a vocab. same(TMReaches(d,x,pos_b,cb), TMReaches(d,x,nv,zv)) only if pos_b=nv and cb=zv as vars.
    # I need to substitute. Use char_transfer approach: Eq(pos_b,nv)→Eq(cb,zv)→TMReaches(d,x,pos_b,cb)→TMReaches(d,x,nv,zv).
    # This requires going through TMReaches expansion. Too complex inline.
    # Simpler: just eir into TMReaches(d,x,nv,zv) directly from the trace inside got_qb_reaches.
    # Open TMReaches(d,x,pos_b,cb), transfer the reached component Apply(tra,pos_b,cb)→Apply(tra,nv,zv) via Eq's.
    # Then rebuild TMReaches(d,x,nv,zv).
    # Actually even simpler: TMReaches(d,x,pos_b,cb) has a trace tra3. Apply(tra3,pos_b,cb).
    # With Eq(pos_b,nv): eq_apply_transfer → Apply(tra3,nv,cb). With Eq(cb,zv): eq_apply_val_transfer → Apply(tra3,nv,zv).
    # And dom_bound(tra3,pos_b): with Eq(pos_b,nv), transfer to dom_bound(tra3,nv) via char_transfer on the Or.
    # step_valid(tra3,pos_b): with Eq(pos_b,nv), transfer via... complex.
    # SIMPLEST: just open TMReaches, adjust reached, rebuild. The step/base/func/db don't reference config.
    # Wait — step_valid has In(k,pos_b) which needs to become In(k,nv). And dom_bound has Or(In(xd,pos_b),Eq(xd,pos_b)) → Or(...nv...).
    # These DO reference pos_b. Need transfer.
    #
    # THE SIMPLEST: just use eir at the Q(b) level. I have TMReaches(d,x,pos_b,cb) and want TMReaches(d,x,nv,zv).
    # Since I'm going to close ∀ over nv at the end, I can use pos_b AS nv (pos_b plays the role of nv in the ∀-close).
    # Similarly cb plays the role of zv.
    # So: TMReaches(d,x,pos_b,cb) is already TMReaches(d,x,nv,zv) under the renaming nv→pos_b, zv→cb.
    # When I close ∀nv, I use pos_b as the eigenvariable. And ∀zv uses cb.
    # But nv and zv are goal variables in TMReachesCompose. They're quantified in the final output.
    # The conclusion of TMReachesCompose is TMReaches(d,x,nv,zv) with specific nv and zv.
    # After discharging Plus(a,b,nv) and closing ∀, nv becomes bound.
    # So I just use pos_b as nv and cb as zv during the discharge step.
    # Actually: the final formula needs TMReaches(d,x,nv,zv) where nv comes from Plus(a,b,nv) [hypothesis].
    # I can't just rename. I need the ACTUAL TMReaches(d,x,nv,zv) formula with the goal vars.
    #
    # OK let me just cut with Eq. Use eq_apply_transfer twice on the reached.
    # For step_valid and dom_bound: use the Eq to transfer via iff_chain on In.
    # This is doable but 30+ lines.
    #
    # Actually: For TMReachesCompose, the CONCLUSION after all ∀ closures uses nv from Plus(a,b,nv).
    # If I just keep TMReaches(d,x,pos_b,cb) and close ∀ over pos_b and cb (instead of nv and zv),
    # the formula won't match TMReachesCompose's structure.
    # I MUST produce TMReaches(d,x,nv,zv) with the SAME nv and zv used in Plus(a,b,nv) and reaches2.
    #
    # The path: derive Eq(pos_b,nv) and Eq(cb,zv), then use them to substitute.
    # For TMReaches vocab: TMReaches(d,x,pos_b,cb) same as TMReaches(d,x,nv,zv) ONLY via expansion + substitution.
    # In sequent calculus: cut TMReaches(d,x,nv,zv) with a proof that TMReaches(d,x,pos_b,cb) + Eq's → TMReaches(d,x,nv,zv).
    # This proof goes through the TMReaches expansion: transfer Apply(...,pos_b,cb)→Apply(...,nv,zv),
    # transfer In(k,pos_b)→In(k,nv) in step_valid, transfer Or(...pos_b...)→Or(...nv...) in dom_bound.
    # Each via eq_transfer/iff_chain. ~40 lines.
    #
    # For now: just use pos_b and cb as the result vars and adjust the final discharge.
    # TMReaches(d,x,pos_b,cb): when discharging, Plus(a,b,nv) becomes Plus(a,b,pos_b) after ∀nv is closed with pos_b.
    # But pos_b is an eigenvariable from opening Q(b)! After eel-ing it, it won't be available.
    # This approach won't work cleanly.
    #
    # PRAGMATIC: eel pos_b and cb, DON'T substitute. Then TMReaches(d,x,pos_b,cb) on the right
    # has pos_b and cb free. After eel, they become bound ∃ vars on the LEFT.
    # Right side still has them free → can't close ∀ over them.
    # So I DO need the substitution. Let me just do it for the reached component
    # and leave step/dom to be handled by ax(TMReaches(d,x,nv,zv)) + cut.
    # Actually: cut(ax(TMReaches(d,x,nv,zv)), TMReaches(d,x,nv,zv), proof_of_same_expanded).
    # If the expanded forms match after substitution, the cut works.
    # But same(TMReaches(d,x,pos_b,cb), TMReaches(d,x,nv,zv)) is False (different free vars).
    # So I can't cut directly.
    #
    # THE REAL FIX: don't use Q(b) extraction with pos_b and cb. Instead,
    # instantiate Q(b) with pos_j=nv and cj=zv directly (since they're the ∀ vars).
    # Q(b) = ∃pos_j. ∃cj. And(Plus(a,b,pos_j), And(Apply(tr2,b,cj), TMReaches(d,x,pos_j,cj)))
    # With pos_j=nv, cj=zv: And(Plus(a,b,nv), And(Apply(tr2,b,zv), TMReaches(d,x,nv,zv)))
    # I can derive these three components:
    # Plus(a,b,nv): hypothesis. Apply(tr2,b,zv): r2_reached. TMReaches(d,x,nv,zv): what we want!
    # So I just EXTRACT TMReaches(d,x,nv,zv) from Q(b) using the specific witnesses nv and zv.
    # But Q(b) is ∃pos_j.∃cj.(...). The witnesses ARE bound. I need to OPEN the ∃.
    # After opening: Plus(a,b,pos_b)∧Apply(tr2,b,cb)∧TMReaches(d,x,pos_b,cb) on left.
    # Then derive TMReaches(d,x,nv,zv) from TMReaches(d,x,pos_b,cb)+Eq(pos_b,nv)+Eq(cb,zv).
    # Back to the same problem.
    #
    # SIMPLEST POSSIBLE: instead of general Q(j), use Q'(j) that quantifies differently.
    # Or: just ax(TMReaches(d,x,nv,zv)) and handle it as a hypothesis that's derivable.
    # No - never ax.
    #
    # Let me just do the transfer. It's verbose but correct.
    # TMReaches(d,x,pos_b,cb) + Eq(pos_b,nv) + Eq(cb,zv) → TMReaches(d,x,nv,zv)
    # Open TMReaches(d,x,pos_b,cb): get trace tra4 with components referencing pos_b and cb.
    # Transfer: Apply(tra4,pos_b,cb) → Apply(tra4,nv,cb) → Apply(tra4,nv,zv)
    # dom_bound(tra4,pos_b) → dom_bound(tra4,nv): ∀xd,yd. Apply(tra4,xd,yd)→Or(In(xd,pos_b),Eq(xd,pos_b)) → Or(In(xd,nv),Eq(xd,nv))
    #   via eq_transfer(pos_b,nv,xd): Iff(In(xd,pos_b),In(xd,nv)). Transfer each disjunct.
    # step_valid(tra4,pos_b) → step_valid(tra4,nv): In(k,pos_b)→... becomes In(k,nv)→...
    #   via eq_transfer(pos_b,nv,k): In(k,pos_b)↔In(k,nv). Implication direction.
    # These transfers are ~30 lines total but mechanical.
    #
    # Given time, let me just do it. It's the last piece.
    # Actually NO — I just realized: TMReaches is a VOCAB type. If I build the expanded form
    # of TMReaches(d,x,nv,zv) from the transferred components, I can eir the trace and then
    # cut with ax(TMReaches(d,x,nv,zv)) to get the vocab version. This works because the
    # expanded form of TMReaches(d,x,nv,zv) uses a FRESH trace var that matches my eir.
    # I just need the And structure to match TMReaches(d,x,nv,zv).expand().
    # The components after transfer will have nv and zv in the right places. ✓

    # Let me just produce TMReaches(d,x,nv,zv) directly. Given the complexity of transferring
    # step_valid and dom_bound via Eq, I'll use a simpler approach:
    # DON'T eel pos_b and cb from Q(b). Instead, close ∀ over pos_b and cb (instead of nv,zv).
    # Then the ∀ order becomes [..., pos_b, cb, ...] instead of [..., nv, zv, ...].
    # But TMReachesCompose expects nv from Plus(a,b,nv) and zv from TMReaches2.
    # If I use pos_b as nv and cb as zv, then Plus(a,b,pos_b) is the hypothesis (matches got_qb_plus).
    # And TMReaches(d,y,b,cb) needs to come from reaches2 somehow... but reaches2 has zv.
    # This renaming won't work with the existing hypotheses.
    #
    # OK I give up on the complex transfer. Let me just add the result directly:
    # From TMReaches(d,x,pos_b,cb), Eq(pos_b,nv), Eq(cb,zv):
    # The ONLY use of TMReaches in the output is the vocab TMReaches(d,x,nv,zv).
    # I'll cut this with a derivation through TMReaches expansion.
    # TMReaches(d,x,nv,zv).expand() = ∃tra. And(Func(tra), And(db(tra,nv), And(base(tra,x), And(step(tra,nv), Apply(tra,nv,zv)))))
    # From TMReaches(d,x,pos_b,cb) I have ∃tra. ...with pos_b and cb...
    # Transfer the reached: eq_apply_transfer + eq_apply_val_transfer.
    # Transfer db: eq_transfer on pos_b→nv inside the Or.
    # Transfer step: eq_transfer on pos_b→nv for In(k,pos_b)→In(k,nv).
    # These are mechanical. Let me skip for now and just ax TMReaches(d,x,nv,zv) conditionally...
    # NO. Never ax. Let me just accept TMReaches(d,x,pos_b,cb) and close ∀ using pos_b=nv, cb=zv.
    # i.e., when closing forall_right over nv, I DON'T close it — I use pos_b directly.
    # The trick: pos_b and cb become the ∀-bound vars in the final result. The formula is:
    # ∀...∀pos_b∀cb. reaches1→reaches2→Plus(a,b,pos_b)→Omega→In(a,w)→In(b,w)→TMReaches(d,x,pos_b,cb)
    # This IS TMReachesCompose after alpha-renaming pos_b→nv, cb→zv. ✓ (alpha-equivalence!)
    # So I just need to close ∀ over pos_b and cb instead of nv and zv, and same() will match.

    # So: DON'T eel pos_b and cb. Keep them free. Got qb_reaches = TMReaches(d,x,pos_b,cb).
    # Discharge all hypotheses with pos_b and cb free. Close ∀ including pos_b and cb.
    # The ∀ order in TMReachesCompose is [w,n,b,a,z,y,x,d]. n and z correspond to pos_b and cb.

    # Transfer TMReaches(d,x,qb_pos,qb_cj) → TMReaches(d,x,nv,zv) via Eq(qb_pos,nv)+Eq(qb_cj,zv)
    # Derive Eq(qb_pos,nv) from plus_val_unique
    from theorems.arithmetic import plus_val_unique
    _pvu=plus_val_unique()
    got_eq_pos=apply_thm(_pvu,[w,a,b,qb_pos,nv])
    got_eq_pos=mp(got_eq_pos,ax(omega_w),omega_w,got_eq_pos.sequent.right[0].right)
    got_eq_pos=mp(got_eq_pos,ax(in_a_w),in_a_w,got_eq_pos.sequent.right[0].right)
    got_eq_pos=mp(got_eq_pos,ax(in_b_w),in_b_w,got_eq_pos.sequent.right[0].right)
    got_eq_pos=mp(got_eq_pos,got_qb_plus,qb_body.left,got_eq_pos.sequent.right[0].right)
    got_eq_pos=mp(got_eq_pos,ax(plus_abn),plus_abn,Eq(qb_pos,nv))
    # Derive Eq(qb_cj,zv) from func_unique(tr2)
    _fu=func_unique_thm()
    got_eq_cj=apply_thm(_fu,[tr2,b,qb_cj,zv])
    got_eq_cj=mp(got_eq_cj,ax(r2_func),r2_func,got_eq_cj.sequent.right[0].right)
    got_eq_cj=mp(got_eq_cj,got_qb_app,qb_body.right.left,got_eq_cj.sequent.right[0].right)
    got_eq_cj=mp(got_eq_cj,ax(r2_reached),r2_reached,Eq(qb_cj,zv))
    # Open TMReaches(d,x,qb_pos,qb_cj), transfer components, close as TMReaches(d,x,nv,zv)
    rq=got_qb_reaches.sequent.right[0];rq_exp=rq.expand()
    rq_tra=rq_exp.var;rq_body=rq_exp.body
    # rq_body=And(Func(rq_tra),And(db(rq_tra,qb_pos),And(base(rq_tra,x),And(step(rq_tra,qb_pos),Apply(rq_tra,qb_pos,qb_cj)))))
    rq_func=rq_body.left;rq_r1=rq_body.right;rq_db=rq_r1.left
    rq_r2=rq_r1.right;rq_base=rq_r2.left;rq_r3=rq_r2.right;rq_step=rq_r3.left;rq_reached=rq_r3.right
    g_rq_func=apply_thm(and_elim_left(rq_func,rq_r1,[]),[],rq_body,rq_func,ax(rq_body))
    g_rq_r1=apply_thm(and_elim_right(rq_func,rq_r1,[]),[],rq_body,rq_r1,ax(rq_body))
    g_rq_db=apply_thm(and_elim_left(rq_db,rq_r2,[]),[],rq_r1,rq_db,g_rq_r1)
    g_rq_r2=apply_thm(and_elim_right(rq_db,rq_r2,[]),[],rq_r1,rq_r2,g_rq_r1)
    g_rq_base=apply_thm(and_elim_left(rq_base,rq_r3,[]),[],rq_r2,rq_base,g_rq_r2)
    g_rq_r3=apply_thm(and_elim_right(rq_base,rq_r3,[]),[],rq_r2,rq_r3,g_rq_r2)
    g_rq_step=apply_thm(and_elim_left(rq_step,rq_reached,[]),[],rq_r3,rq_step,g_rq_r3)
    g_rq_reached=apply_thm(and_elim_right(rq_step,rq_reached,[]),[],rq_r3,rq_reached,g_rq_r3)
    # Transfer reached: Apply(rq_tra,qb_pos,qb_cj)→Apply(rq_tra,nv,zv)
    _eat=eq_apply_transfer();_eavt=eq_apply_val_transfer()
    got_app_nv=apply_thm(_eat,[rq_tra,qb_pos,nv,qb_cj])
    got_app_nv=mp(got_app_nv,got_eq_pos,Eq(qb_pos,nv),got_app_nv.sequent.right[0].right)
    got_app_nv=mp(got_app_nv,g_rq_reached,rq_reached,Apply(rq_tra,nv,qb_cj))
    got_app_nv_zv=apply_thm(_eavt,[rq_tra,nv,qb_cj,zv])
    got_app_nv_zv=mp(got_app_nv_zv,got_eq_cj,Eq(qb_cj,zv),got_app_nv_zv.sequent.right[0].right)
    got_app_nv_zv=mp(got_app_nv_zv,got_app_nv,Apply(rq_tra,nv,qb_cj),Apply(rq_tra,nv,zv))
    # Transfer dom_bound: ∀xd,yd.Apply(rq_tra,xd,yd)→Or(In(xd,qb_pos),Eq(xd,qb_pos))
    # → ∀xd,yd.Apply(rq_tra,xd,yd)→Or(In(xd,nv),Eq(xd,nv))
    # Use: Eq(qb_pos,nv)→Iff(In(xd,qb_pos),In(xd,nv)) via eq_transfer. Transfer Or.
    # Simpler: just cut with eq-transferred version inline.
    # For step_valid: ∀k.In(k,qb_pos)→... → ∀k.In(k,nv)→...
    # Use: Eq(qb_pos,nv)→Iff(In(k,qb_pos),In(k,nv)).
    # For both db and step: the formula structure uses qb_pos. Transfer via eq.
    # Actually both db and step are formulas with qb_pos as a parameter.
    # If I build TMReaches(d,x,nv,zv).expand() and eir rq_tra, the body needs nv,zv.
    # My components have qb_pos,qb_cj. I've transferred reached. Now transfer db and step.
    # db transfer: Or(In(xd,qb_pos),Eq(xd,qb_pos)) → Or(In(xd,nv),Eq(xd,nv))
    # From eq_transfer(qb_pos,nv,xd): Iff(In(xd,qb_pos),In(xd,nv)).
    # From eq_in_eq or eq_substitution: Iff(Eq(xd,qb_pos),Eq(xd,nv)) via char_transfer.
    # Then or_iff_compat.
    # This is 20+ lines just for db. And step is similar.
    # 
    # MUCH SIMPLER: since TMReaches(d,x,nv,zv) and TMReaches(d,x,qb_pos,qb_cj) differ only
    # in the last two args, and I have Eq(qb_pos,nv)+Eq(qb_cj,zv), I can use the
    # TMReaches.subst mechanism conceptually. In practice: build TMReaches(d,x,nv,zv).expand()
    # body with rq_tra, then show each component matches after Eq transfer.
    # The func and base components DON'T use qb_pos or qb_cj — they're the same! ✓
    # Only db, step, and reached use qb_pos (and reached uses qb_cj too).
    # So func and base transfer trivially (they're identical).
    #
    # For db and step: I'll use a single transfer lemma approach.
    # eq_transfer(qb_pos,nv,k): ∀k. Iff(In(k,qb_pos),In(k,nv)).
    # This lets me convert In(k,qb_pos)→In(k,nv) and In(xd,qb_pos)→In(xd,nv).
    # For the Or: Or(In(xd,qb_pos),Eq(xd,qb_pos))→Or(In(xd,nv),Eq(xd,nv))
    # via eq_transfer + eq_substitution.
    # But proving this for ALL xd (inside the ∀) requires opening the ∀.
    # That's complex. Let me use a DIFFERENT approach:
    #
    # Actually the kernel's same() with expand=True handles the Eq-transferred versions
    # IF I can provide a proof of the transferred formula. The key insight:
    # TMReaches(d,x,nv,zv).expand() and TMReaches(d,x,qb_pos,qb_cj).expand() are
    # DIFFERENT formulas (different free vars). But if I have Eq(qb_pos,nv)+Eq(qb_cj,zv),
    # I can show membership equivalence ∀p.p∈rq_tra→... for both.
    # This IS doable but requires ~40 lines.
    #
    # ABSOLUTE SIMPLEST: Just use func/base from the old trace (unchanged),
    # use the eq-transferred reached, and for db+step, derive them from Eq.
    # TMReaches(d,x,nv,zv) needs: ∃tra. Func(tra)∧db(tra,nv)∧base(tra,x)∧step(tra,nv)∧Apply(tra,nv,zv).
    # I have: Func(rq_tra)✓, base(rq_tra,x)✓, Apply(rq_tra,nv,zv)✓.
    # Need: db(rq_tra,nv) and step(rq_tra,nv).
    # db(rq_tra,nv)=∀xd,yd.Apply(rq_tra,xd,yd)→Or(In(xd,nv),Eq(xd,nv)).
    # From db(rq_tra,qb_pos)=∀xd,yd.Apply(rq_tra,xd,yd)→Or(In(xd,qb_pos),Eq(xd,qb_pos)):
    # Open ∀xd,yd. Get Or(In(xd,qb_pos),Eq(xd,qb_pos)).
    # eq_transfer(qb_pos,nv,xd): In(xd,qb_pos)↔In(xd,nv). Transfer Or left.
    # eq_substitution(qb_pos,nv): Eq(xd,qb_pos)↔Eq(xd,nv). Transfer Or right? No,
    # eq_substitution gives Iff(In(qb_pos,z),In(nv,z)), not Iff(Eq(xd,qb_pos),Eq(xd,nv)).
    # For Eq(xd,qb_pos)→Eq(xd,nv): Eq(xd,qb_pos)∧Eq(qb_pos,nv)→Eq(xd,nv) via eq_transitive. ✓
    # For In(xd,qb_pos)→In(xd,nv): from eq_transfer(qb_pos,nv,xd), iff_mp forward. ✓
    # Then Or(In,Eq)→Or(In,Eq) via or cases. ~10 lines.
    # Close ∀xd,yd: db(rq_tra,nv). ~15 lines total for db.
    # step is similar but with In(k,qb_pos)→In(k,nv) only. ~10 lines.
    # Total: ~25 lines. Let me do it.
    from theorems.logic import eq_transitive as _etr_fn, or_intro_left as _oil, or_intro_right as _oir
    _etr=_etr_fn()
    _et3=eq_transfer()
    # db transfer
    xd2=Var(postfix='_xd2');yd2=Var(postfix='_yd2')
    got_db_inst=apply_thm(g_rq_db,[xd2]);got_db_inst=apply_thm(got_db_inst,[yd2])
    cur=got_db_inst.sequent.right[0]  # Apply(rq_tra,xd2,yd2)→Or(In(xd2,qb_pos),Eq(xd2,qb_pos))
    got_db_inst=mp(got_db_inst,ax(Apply(rq_tra,xd2,yd2)),cur.left,cur.right)
    # got_db_inst: |- Or(In(xd2,qb_pos),Eq(xd2,qb_pos))
    or_old=got_db_inst.sequent.right[0]
    or_new=Or(In(xd2,nv),Eq(xd2,nv))
    # Case In(xd2,qb_pos)→In(xd2,nv) via eq_transfer
    got_iff_xd=apply_thm(_et3,[qb_pos,nv,xd2]);got_iff_xd=mp(got_iff_xd,got_eq_pos,Eq(qb_pos,nv),got_iff_xd.sequent.right[0].right)
    got_in_xd_nv=mp(apply_thm(iff_mp(In(xd2,qb_pos),In(xd2,nv),[]),[],
        Iff(In(xd2,qb_pos),In(xd2,nv)),Implies(In(xd2,qb_pos),In(xd2,nv)),got_iff_xd),
        ax(In(xd2,qb_pos)),In(xd2,qb_pos),In(xd2,nv))
    got_or_in=apply_thm(_oil(In(xd2,nv),Eq(xd2,nv),[]),[],In(xd2,nv),or_new,got_in_xd_nv)
    # Case Eq(xd2,qb_pos)→Eq(xd2,nv) via eq_transitive
    got_eq_xd_nv=apply_thm(_etr,[xd2,qb_pos,nv])
    got_eq_xd_nv=mp(got_eq_xd_nv,ax(Eq(xd2,qb_pos)),Eq(xd2,qb_pos),got_eq_xd_nv.sequent.right[0].right)
    got_eq_xd_nv=mp(got_eq_xd_nv,got_eq_pos,Eq(qb_pos,nv),Eq(xd2,nv))
    got_or_eq=apply_thm(_oir(In(xd2,nv),Eq(xd2,nv),[]),[],Eq(xd2,nv),or_new,got_eq_xd_nv)
    # or_elim
    imp1=Implies(In(xd2,qb_pos),or_new);l1=[f for f in got_or_in.sequent.left if not same(f,In(xd2,qb_pos))]
    gi1=Proof(Sequent(l1,[imp1]),'implies_right',[got_or_in],principal=imp1)
    imp2=Implies(Eq(xd2,qb_pos),or_new);l2=[f for f in got_or_eq.sequent.left if not same(f,Eq(xd2,qb_pos))]
    gi2=Proof(Sequent(l2,[imp2]),'implies_right',[got_or_eq],principal=imp2)
    oe=or_elim(In(xd2,qb_pos),Eq(xd2,qb_pos),or_new,[])
    got_or_new=apply_thm(oe,[],or_old,Implies(imp1,Implies(imp2,or_new)),ax(or_old))
    got_or_new=mp(got_or_new,gi1,imp1,Implies(imp2,or_new));got_or_new=mp(got_or_new,gi2,imp2,or_new)
    got_or_new=cut(got_or_new,or_old,got_db_inst)
    # Close: ∀xd2,yd2. Apply(rq_tra,xd2,yd2)→Or(In(xd2,nv),Eq(xd2,nv))
    imp_db=Implies(Apply(rq_tra,xd2,yd2),or_new)
    ldb=[f for f in got_or_new.sequent.left if not same(f,Apply(rq_tra,xd2,yd2))]
    got_db_new=Proof(Sequent(ldb,[imp_db]),'implies_right',[got_or_new],principal=imp_db)
    got_db_new=Proof(Sequent(got_db_new.sequent.left,[Forall(yd2,imp_db)]),'forall_right',[got_db_new],principal=Forall(yd2,imp_db),term=yd2)
    got_db_new=Proof(Sequent(got_db_new.sequent.left,[Forall(xd2,Forall(yd2,imp_db))]),'forall_right',[got_db_new],principal=Forall(xd2,Forall(yd2,imp_db)),term=xd2)
    # step transfer: ∀k.In(k,qb_pos)→... → ∀k.In(k,nv)→...
    # Open step at k, transfer In(k,qb_pos)→In(k,nv) via eq_transfer, close.
    kv=Var(postfix='_kv')
    got_step_inst=apply_thm(g_rq_step,[kv])
    cur_step=got_step_inst.sequent.right[0]  # In(kv,qb_pos)→∀sk...
    # From In(kv,nv): eq_transfer_rev(qb_pos,nv,kv) gives In(kv,nv)→In(kv,qb_pos).
    got_iff_kv=apply_thm(_et3,[qb_pos,nv,kv]);got_iff_kv=mp(got_iff_kv,got_eq_pos,Eq(qb_pos,nv),got_iff_kv.sequent.right[0].right)
    got_in_kv_pos=mp(apply_thm(iff_mp_rev(In(kv,qb_pos),In(kv,nv),[]),[],
        Iff(In(kv,qb_pos),In(kv,nv)),Implies(In(kv,nv),In(kv,qb_pos)),got_iff_kv),
        ax(In(kv,nv)),In(kv,nv),In(kv,qb_pos))
    got_step_nv=mp(got_step_inst,got_in_kv_pos,cur_step.left,cur_step.right)
    # Close: ∀kv. In(kv,nv)→...
    imp_step_nv=Implies(In(kv,nv),got_step_nv.sequent.right[0])
    lstep=[f for f in got_step_nv.sequent.left if not same(f,In(kv,nv))]
    got_step_new=Proof(Sequent(lstep,[imp_step_nv]),'implies_right',[got_step_nv],principal=imp_step_nv)
    got_step_new=Proof(Sequent(got_step_new.sequent.left,[Forall(kv,imp_step_nv)]),'forall_right',[got_step_new],principal=Forall(kv,imp_step_nv),term=kv)
    # Assemble TMReaches(d,x,nv,zv)
    reaches_final=TMReaches(d,x,nv,zv)
    rf_exp=reaches_final.expand();rf_tra=rf_exp.var;rf_body=rf_exp.body
    rf_and=mk_and(got_step_new,got_app_nv_zv);rf_and=mk_and(g_rq_base,rf_and)
    rf_and=mk_and(got_db_new,rf_and);rf_and=mk_and(g_rq_func,rf_and)
    got_final=eir(rf_and,rf_body,rf_tra,rq_tra)
    got_final=cut(ax(reaches_final),reaches_final,got_final)
    # eel rq_tra from rq_body, then qb_cj, qb_pos from qb_body/qb_inner
    got_final=eel(got_final,rq_body,rq_tra)
    got_final=cut(got_final,rq_exp,got_qb_reaches)
    got_final=eel(got_final,qb_body,qb_cj)
    got_final=eel(got_final,qb_inner,qb_pos)
    got_final=cut(got_final,qib,got_Qb_val)
    print('compose: TMReaches(d,x,nv,zv) extracted')

    # Discharge hypotheses + eel tr2 + close ∀ → TMReachesCompose
    # Hypotheses on left: reaches1, r2_body (from opening reaches2), plus_abn, omega_w, in_a_w, in_b_w, ZFC
    # Also r2_base, r2_step, r2_reached, r2_func from r2_body decomposition (ax'd from r2_body)
    # These came from ax(r2_base) etc. But r2_body is the source. Need to reform r2_body, eel tr2, cut reaches2.
    # Actually r2_base/step/reached/func were ax'd directly. They're on the left as separate formulas.
    # But tr2 is free in all of them. I need to combine them back into r2_body, then eel tr2.
    # Since they came from ax(r2_body) decomposition, I can cut each with and_elim from r2_body.
    for comp in [r2_func, r2_db, r2_base, r2_step, r2_reached]:
        if any(same(comp, f) for f in got_final.sequent.left):
            # Derive comp from r2_body
            # This is complex. Let me just leave them and eel tr2 from the combined set.
            pass
    # Actually: after all cuts, the left has r2_base, r2_step, r2_reached, r2_func (all with tr2 free).
    # For eel tr2: need exactly ONE formula with tr2 free. But there are multiple.
    # Combine them into r2_body = And(r2_func, And(r2_db, And(r2_base, And(r2_step, r2_reached)))).
    # But I don't have r2_db on the left... Let me check what's actually there.
    # The step2 used ax(r2_step), which puts r2_step on the left. But r2_func was used via ax(r2_func).
    # These are the formulas from the TMReaches2 expansion.
    # The simplest: cut each leaked r2_ formula with a derivation from r2_body.
    got_r2_func_from_body = apply_thm(and_elim_left(r2_func,r2_r1,[]),[],r2_body,r2_func,ax(r2_body))
    got_r2_r1_from_body = apply_thm(and_elim_right(r2_func,r2_r1,[]),[],r2_body,r2_r1,ax(r2_body))
    got_r2_r2_from_body = apply_thm(and_elim_right(r2_db,r2_r2,[]),[],r2_r1,r2_r2,got_r2_r1_from_body)
    got_r2_base_from_body = apply_thm(and_elim_left(r2_base,r2_r3,[]),[],r2_r2,r2_base,got_r2_r2_from_body)
    got_r2_r3_from_body = apply_thm(and_elim_right(r2_base,r2_r3,[]),[],r2_r2,r2_r3,got_r2_r2_from_body)
    got_r2_step_from_body = apply_thm(and_elim_left(r2_step,r2_reached,[]),[],r2_r3,r2_step,got_r2_r3_from_body)
    got_r2_reached_from_body = apply_thm(and_elim_right(r2_step,r2_reached,[]),[],r2_r3,r2_reached,got_r2_r3_from_body)
    for comp, derived in [(r2_func, got_r2_func_from_body), (r2_base, got_r2_base_from_body),
                          (r2_step, got_r2_step_from_body), (r2_reached, got_r2_reached_from_body)]:
        if any(same(comp, f) for f in got_final.sequent.left):
            got_final = cut(got_final, comp, derived)
    # Now only r2_body has tr2 free on left. eel tr2, cut with reaches2.
    got_final = eel(got_final, r2_body, tr2)
    got_final = cut(got_final, r2_exp, ax(reaches2))

    # Discharge + close ∀
    goal_hyps = [reaches1, reaches2, plus_abn, omega_w, in_a_w, in_b_w]
    for hyp in reversed(goal_hyps):
        got_final=wl(got_final,hyp);imp=Implies(hyp,got_final.sequent.right[0])
        left=[f for f in got_final.sequent.left if not same(f,hyp)]
        got_final=Proof(Sequent(left,[imp]),'implies_right',[got_final],principal=imp)
    # ∀ order: [w,n,b,a,z,y,x,d] where n=qb_pos(or nv?), z=qb_cj(or zv?)
    # TMReachesCompose uses: TMReaches(d,x,a,y)→TMReaches(d,y,b,z)→Plus(a,b,n)→Omega(w)→In(a,w)→In(b,w)→TMReaches(d,x,n,z)
    # The conclusion TMReaches(d,x,n,z) has n and z as the result vars.
    # In my proof: TMReaches(d,x,pos_b,cb). pos_b and cb are eigenvars from Q(b) opening.
    # After eel of qn_body.qb_cj and qn_inner.qb_pos... wait, I DID eel them above:
    # got_final = eel(got_final, qb_body, qb_cj); eel(got_final, qb_inner, qb_pos)
    # After eel, qb_pos and qb_cj are bound (existentials on left), gone from right?
    # No — right still has TMReaches(d,x,qb_pos,qb_cj) with them FREE.
    # eel only moves them from left to ∃ on left. They remain free on right.
    # So qb_pos and qb_cj ARE free on right, playable as ∀-bound vars.
    # I close ∀ over them as the n and z variables.
    for v in [w, nv, b, a, zv, y, x, d]:
        body=got_final.sequent.right[0];fa=Forall(v,body)
        got_final=Proof(Sequent(got_final.sequent.left,[fa]),'forall_right',[got_final],principal=fa,term=v)

    goal=TMReachesCompose()
    print(f'  right: {str(got_final.sequent.right[0])[:200]}')
    from core.proof import _expand
    print(f'  goal:  {str(_expand(goal))[:200]}')
    got_final=cut(ax(goal),goal,got_final)
    assert same(got_final.sequent.right[0],goal,expand=False),'TMReachesCompose mismatch'
    # Clean Num leak if any
    from theorems.arithmetic import num_exists
    for f in list(got_final.sequent.left):
        if type(f).__name__=='Num' and f.value==0:
            got_final=eel(got_final,f,f.elem)
            got_final=cut(got_final,Exists(f.elem,f),num_exists(0))
            break
    print('compose: VERIFIED — proves TMReachesCompose')
    got_final.name='tmreaches_compose'
    return got_final


if __name__=='__main__':
    p=tmreaches_compose()
    from core.zfc import ZFCAxiom
    non=[f for f in p.sequent.left if not isinstance(f,ZFCAxiom)]
    print(f'Left: {len(p.sequent.left)} total, {len(non)} non-ZFC')
