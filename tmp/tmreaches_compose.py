"""TMReachesCompose: chain two TMReaches.

Q(j) = ∃pos_j,cj. Plus(a,j,pos_j) ∧ Apply(tr2,j,cj) ∧ TMReaches(d,x,pos_j,cj)
Base j=0: Plus(a,0,a), Apply(tr2,0,y), TMReaches(d,x,a,y).
Step: extend TMReaches by one TMStep from trace2's step_valid.
  Open TMReaches(d,x,pos_j,cj) → get trace1 with Function.
  tape_update_exists to extend trace1 at S(pos_j). Rebuild TMReaches.
At j=b: Plus(a,b,n), Apply(tr2,b,z), TMReaches(d,x,n,z).
"""
import sys; sys.path.insert(0, '/root/min/src')
from core.lang import Var, In, Not, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq
from core.proof import Proof, Sequent, same, _var_free_in_sequent
from vocab.ordpair import OrdPair, Successor
from vocab.omega import Omega, Num
from vocab.sets import Empty
from vocab.tm import TMConfig, TMTransition, TMStep, TMReaches, TapeUpdate
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
from theorems.arithmetic import (plus_zero_exists, plus_succ_right, plus_val_in_omega)
from theorems.recursion import eq_apply_transfer, eq_apply_val_transfer
from theorems.tm import (TMReachesCompose, tape_update_exists, tape_update_at,
    tape_update_other, tape_update_other_rev, tape_update_function)
from vocab.sets import TransitiveSet
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

    # Open TMReaches2: ∃tr2. And(Function(tr2), And(base2, And(step2, reached2)))
    r2_exp=reaches2.expand();tr2=r2_exp.var;r2_body=r2_exp.body
    r2_func=r2_body.left  # Function(tr2)
    r2_inner=r2_body.right
    r2_base=r2_inner.left
    r2_rest=r2_inner.right
    r2_step=r2_rest.left
    r2_reached=r2_rest.right  # Apply(tr2,b,zv)

    # Q(j) = ∃pos_j,cj. Plus(a,j,pos_j) ∧ Apply(tr2,j,cj) ∧ TMReaches(d,x,pos_j,cj)
    j=Var(postfix='j');pos_j=Var(postfix='pj');cj=Var(postfix='cj')
    def Q(jj):
        return Exists(pos_j, Exists(cj, And(PlusDef(a,jj,pos_j),
            And(Apply(tr2,jj,cj), TMReaches(d,x,pos_j,cj)))))

    # Separation
    pv=Var(postfix='ind_pv');xv=Var(postfix='ind_xv')
    sep=zfc.Separation(Q,[a,d,x,tr2,pos_j,cj])
    sep_ax=Proof(Sequent([sep],[sep]),'axiom',principal=sep)
    char_pv=Forall(xv,Iff(In(xv,pv),And(In(xv,w),Q(xv))))
    got_ex_pv=apply_thm(sep_ax,[cj,pos_j,tr2,x,d,a,w],concl=Exists(pv,char_pv))
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
    # Plus(a,z,a)
    _pze=plus_zero_exists()
    got_plus_az=apply_thm(_pze,[w,a,z])
    got_plus_az=mp(got_plus_az,ax(omega_w),omega_w,got_plus_az.sequent.right[0].right)
    got_plus_az=mp(got_plus_az,ax(in_a_w),in_a_w,got_plus_az.sequent.right[0].right)
    got_plus_az=mp(got_plus_az,ax(num_z),num_z,got_plus_az.sequent.right[0].right)
    # Apply(tr2,z,y) from base2
    got_app_z_y=apply_thm(ax(r2_base),[z]);cur=got_app_z_y.sequent.right[0]
    got_app_z_y=mp(got_app_z_y,ax(num_z),cur.left,cur.right)
    # Assemble Q(z)
    from core.proof import _subst
    q_z=Q(z);q_z_pos=q_z.var;q_z_inner=q_z.body;q_z_cj=q_z_inner.var;q_z_body=q_z_inner.body
    got_q=mk_and(got_app_z_y,ax(reaches1))
    got_q=mk_and(got_plus_az,got_q)
    body_cj=_subst(q_z_body,q_z_pos,a)
    got_ecj=eir(got_q,body_cj,q_z_cj,y)
    got_epos=eir(got_ecj,q_z_inner,q_z_pos,a)
    assert same(got_epos.sequent.right[0],q_z),'Q(z) mismatch'
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
    got_in_nw=apply_thm(and_elim_left(In(n,w),Implies(Or(In(n,b),Eq(n,b)),Q(n)),[]),[],got_an.sequent.right[0],In(n,w),got_an)
    got_Qn_imp=apply_thm(and_elim_right(In(n,w),Implies(Or(In(n,b),Eq(n,b)),Q(n)),[]),[],got_an.sequent.right[0],Implies(Or(In(n,b),Eq(n,b)),Q(n)),got_an)
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
    # Q(n) from IH
    or_nb=Or(In(n,b),Eq(n,b))
    got_ornb=apply_thm(or_intro_left(In(n,b),Eq(n,b),[]),[],In(n,b),or_nb,got_inb)
    got_Q2n=mp(got_Qn_imp,got_ornb,or_nb,Q(n))
    # Open Q(n)
    qn=Q(n);qn_pos=qn.var;qn_inner=qn.body;qn_cj=qn_inner.var;qn_body=qn_inner.body
    got_plus_n=apply_thm(and_elim_left(qn_body.left,qn_body.right,[]),[],qn_body,qn_body.left,ax(qn_body))
    got_rest_n=apply_thm(and_elim_right(qn_body.left,qn_body.right,[]),[],qn_body,qn_body.right,ax(qn_body))
    got_app_n=apply_thm(and_elim_left(qn_body.right.left,qn_body.right.right,[]),[],qn_body.right,qn_body.right.left,got_rest_n)
    got_reaches_n=apply_thm(and_elim_right(qn_body.right.left,qn_body.right.right,[]),[],qn_body.right,qn_body.right.right,got_rest_n)
    print('compose step: Q(n) decomposed')

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
    print('compose step: step2 decomposed')

    # Open TMReaches(d,x,pos_j,cj) to get trace with Function
    r_n=got_reaches_n.sequent.right[0]  # TMReaches(d,x,qn_pos,qn_cj)
    rn_exp=r_n.expand();rn_tra=rn_exp.var;rn_body=rn_exp.body
    rn_func=rn_body.left  # Function(rn_tra)
    rn_inner=rn_body.right
    rn_base=rn_inner.left;rn_rest=rn_inner.right;rn_step=rn_rest.left;rn_reached=rn_rest.right
    got_rn_func=apply_thm(and_elim_left(rn_func,rn_inner,[]),[],rn_body,rn_func,ax(rn_body))
    got_rn_inner=apply_thm(and_elim_right(rn_func,rn_inner,[]),[],rn_body,rn_inner,ax(rn_body))
    got_rn_base=apply_thm(and_elim_left(rn_base,rn_rest,[]),[],rn_inner,rn_base,got_rn_inner)
    got_rn_rest=apply_thm(and_elim_right(rn_base,rn_rest,[]),[],rn_inner,rn_rest,got_rn_inner)
    got_rn_step=apply_thm(and_elim_left(rn_step,rn_reached,[]),[],rn_rest,rn_step,got_rn_rest)
    got_rn_reached=apply_thm(and_elim_right(rn_step,rn_reached,[]),[],rn_rest,rn_reached,got_rn_rest)

    # Successor(spos, qn_pos)
    spos=Var(postfix='spos');succ_spos=Successor(spos,qn_pos)
    got_ex_spos=apply_thm(successor_exists(),[qn_pos],concl=Exists(spos,succ_spos))

    # tape_update_exists: ∃tra3. TapeUpdate(tra3, rn_tra, spos, ck1_var)
    tra3=Var(postfix='tra3');tu_tra3=TapeUpdate(tra3,rn_tra,spos,ck1_var)
    _tue=tape_update_exists()
    got_ex_tra3=apply_thm(_tue,[ck1_var,spos,rn_tra],concl=Exists(tra3,tu_tra3))

    # Function(tra3) from tape_update_function
    _tuf=tape_update_function()
    got_func_tra3=apply_thm(_tuf,[tra3,rn_tra,spos,ck1_var])
    got_func_tra3=mp(got_func_tra3,ax(tu_tra3),tu_tra3,got_func_tra3.sequent.right[0].right)
    got_func_tra3=mp(got_func_tra3,got_rn_func,rn_func,FuncDef(tra3))

    # base3: ∀zp. Empty(zp)→Apply(tra3,zp,x)
    # From rn_base + tape_update_other (zp≠spos since zp is empty, spos=S(qn_pos) is not)
    zp=Var(postfix='_zp')
    got_rnb_inst=apply_thm(got_rn_base,[zp]);cur=got_rnb_inst.sequent.right[0]
    got_app_rn_zp=mp(got_rnb_inst,ax(Empty(zp)),cur.left,cur.right)
    # Not(Eq(zp,spos)): Empty(zp)+In(qn_pos,spos)→contradiction if Eq(zp,spos)
    or_pp=Or(In(qn_pos,qn_pos),Eq(qn_pos,qn_pos))
    iff_pp=Iff(In(qn_pos,spos),or_pp)
    got_iff_pp=apply_thm(ax(succ_spos),[qn_pos],concl=iff_pp)
    got_or_pp=apply_thm(or_intro_right(In(qn_pos,qn_pos),Eq(qn_pos,qn_pos),[]),[],
        Eq(qn_pos,qn_pos),or_pp,apply_thm(eq_reflexive(),[qn_pos]))
    got_in_pos_spos=mp(apply_thm(iff_mp_rev(In(qn_pos,spos),or_pp,[]),[],iff_pp,Implies(or_pp,In(qn_pos,spos)),got_iff_pp),
        got_or_pp,or_pp,In(qn_pos,spos))
    _et2=eq_transfer()
    got_iff_zps=apply_thm(_et2,[zp,spos,qn_pos])
    got_iff_zps=mp(got_iff_zps,ax(Eq(zp,spos)),Eq(zp,spos),got_iff_zps.sequent.right[0].right)
    got_in_pos_zp=mp(apply_thm(iff_mp_rev(In(qn_pos,zp),In(qn_pos,spos),[]),[],
        Iff(In(qn_pos,zp),In(qn_pos,spos)),Implies(In(qn_pos,spos),In(qn_pos,zp)),got_iff_zps),
        got_in_pos_spos,In(qn_pos,spos),In(qn_pos,zp))
    got_not_in=apply_thm(ax(Empty(zp)),[qn_pos])
    not_eq_zp_spos=Not(Eq(zp,spos))
    got_bot=Proof(Sequent([In(qn_pos,zp),Not(In(qn_pos,zp))],[]),'not_left',[ax(In(qn_pos,zp))],principal=Not(In(qn_pos,zp)))
    got_bot=cut(got_bot,Not(In(qn_pos,zp)),got_not_in);got_bot=cut(got_bot,In(qn_pos,zp),got_in_pos_zp)
    got_imp_eq=Proof(Sequent([f for f in got_bot.sequent.left if not same(f,Eq(zp,spos))],[Implies(Eq(zp,spos),not_eq_zp_spos)]),
        'implies_right',[Proof(Sequent(got_bot.sequent.left,[not_eq_zp_spos]),'weakening_right',[got_bot],principal=not_eq_zp_spos)],
        principal=Implies(Eq(zp,spos),not_eq_zp_spos))
    got_lem=Proof(Sequent([],[not_eq_zp_spos,Eq(zp,spos)]),'not_right',
        [Proof(Sequent([Eq(zp,spos)],[Eq(zp,spos)]),'axiom',principal=Eq(zp,spos))],principal=not_eq_zp_spos)
    got_use=Proof(Sequent([Implies(Eq(zp,spos),not_eq_zp_spos)],[not_eq_zp_spos]),'implies_left',
        [got_lem,ax(not_eq_zp_spos)],principal=Implies(Eq(zp,spos),not_eq_zp_spos))
    got_not_eq_zp=cut(got_use,Implies(Eq(zp,spos),not_eq_zp_spos),got_imp_eq)
    # tape_update_other
    _tuo=tape_update_other()
    got_app_tra3_zp=apply_thm(_tuo,[tra3,rn_tra,spos,ck1_var,zp,x])
    got_app_tra3_zp=mp(got_app_tra3_zp,ax(tu_tra3),tu_tra3,got_app_tra3_zp.sequent.right[0].right)
    got_app_tra3_zp=mp(got_app_tra3_zp,got_app_rn_zp,Apply(rn_tra,zp,x),got_app_tra3_zp.sequent.right[0].right)
    got_app_tra3_zp=mp(got_app_tra3_zp,got_not_eq_zp,not_eq_zp_spos,Apply(tra3,zp,x))
    imp_b3=Implies(Empty(zp),Apply(tra3,zp,x));lb3=[f for f in got_app_tra3_zp.sequent.left if not same(f,Empty(zp))]
    got_base3=Proof(Sequent(lb3,[imp_b3]),'implies_right',[got_app_tra3_zp],principal=imp_b3)
    got_base3=Proof(Sequent(got_base3.sequent.left,[Forall(zp,imp_b3)]),'forall_right',[got_base3],principal=Forall(zp,imp_b3),term=zp)
    print('compose step: base3 done')

    # step_valid3: ∀k∈spos. ...
    # For k∈spos: k∈qn_pos ∨ k=qn_pos (from Successor).
    # k∈qn_pos: use rn_step (old trace's step_valid), transfer via tape_update_other.
    # k=qn_pos: func_unique on old trace gives ck_v=cj. TMStep(d,cj,ck1). Transfer via tape_update_at.
    sv_k=Var(postfix='_svk');sv_sk=Var(postfix='_svsk');sv_ck=Var(postfix='_svck');sv_ck1=Var(postfix='_svck1')
    app_tra3_k_ck=Apply(tra3,sv_k,sv_ck)
    app_tra3_sk_ck1=Apply(tra3,sv_sk,sv_ck1)
    sv_goal=Exists(sv_ck1,And(app_tra3_sk_ck1,TMStep(d,sv_ck,sv_ck1)))
    sv_body=Forall(sv_sk,Implies(Successor(sv_sk,sv_k),Forall(sv_ck,Implies(app_tra3_k_ck,sv_goal))))
    # Split on k∈qn_pos ∨ k=qn_pos from Successor(spos,qn_pos)
    or_k=Or(In(sv_k,qn_pos),Eq(sv_k,qn_pos))
    iff_k_spos=Iff(In(sv_k,spos),or_k)
    got_iff_k=apply_thm(ax(succ_spos),[sv_k],concl=iff_k_spos)
    got_k_or=mp(apply_thm(iff_mp(In(sv_k,spos),or_k,[]),[],iff_k_spos,Implies(In(sv_k,spos),or_k),got_iff_k),
        ax(In(sv_k,spos)),In(sv_k,spos),or_k)

    # Case k∈qn_pos: old step_valid handles it
    # rn_step: ∀k∈qn_pos. ∀sk.Succ(sk,k)→∀ck.Apply(rn_tra,k,ck)→∃ck1.And(Apply(rn_tra,sk,ck1),TMStep(d,ck,ck1))
    # Transfer: Apply(tra3,k,ck)→Apply(rn_tra,k,ck) via tape_update_other_rev (k≠spos since k∈qn_pos, omega: k<qn_pos<spos).
    # And Apply(rn_tra,sk,ck1)→Apply(tra3,sk,ck1) via tape_update_other (sk≠spos since S(k)<S(qn_pos)=spos... wait S(k) could equal spos if k=qn_pos. But k∈qn_pos means k≠qn_pos (no self-membership). So S(k)≠S(qn_pos)=spos? Need succ_injection converse... actually k≠qn_pos doesn't immediately give S(k)≠spos. It gives S(k)≠S(qn_pos) IF successor is injective. Which needs omega.
    # For k∈qn_pos: k<qn_pos in omega. S(k)≤qn_pos<spos. So S(k)≠spos.
    # But proving this formally requires omega ordering. Complex.
    # Simpler: handle this via LEM on Eq(sk,spos).
    #   If Eq(sk,spos): Apply(tra3,spos,ck1_var)=tape_update_at. TMStep(d,ck,ck1_var) from... hmm we need ck=cj.
    #   If Not(Eq(sk,spos)): tape_update_other gives Apply(tra3,sk,ck1_v)←Apply(rn_tra,sk,ck1_v). ✓
    #
    # For the Eq(sk,spos) sub-case in k∈qn_pos: sk=S(k). spos=S(qn_pos). If S(k)=S(qn_pos) then k=qn_pos (succ_injection).
    # But k∈qn_pos means k<qn_pos → k≠qn_pos → contradiction. So Eq(sk,spos) is impossible for k∈qn_pos. ✓
    # But proving this needs succ_injection + omega. We have omega from the context.
    #
    # Actually this is getting too complex for this sub-case. Let me use a simpler approach:
    # For k∈qn_pos: Not(Eq(sv_k,spos)) because k∈qn_pos∈S(qn_pos)=spos means k<qn_pos<spos.
    # More directly: k∈qn_pos → k≠qn_pos (omega no-self). qn_pos∈spos. If k=spos then k∈qn_pos∧qn_pos∈k=spos → qn_pos∈spos. But also k=spos=S(qn_pos)∋qn_pos → In(qn_pos,k). And In(k,qn_pos). Cycle → contradiction (omega is well-founded).
    # This needs omega context. We have Omega(w) but not In(qn_pos,w) directly.
    # qn_pos came from Q(n) which has Plus(a,n,qn_pos). plus_val_in_omega gives In(qn_pos,w).
    # Then omega ordering gives the needed inequalities.
    #
    # This is 50+ lines just for Not(Eq(sv_k,spos)) in the k∈qn_pos case.
    # And similarly Not(Eq(sv_sk,spos)) for the same case.
    #
    # Given the enormous complexity, let me use a MUCH simpler approach:
    # Instead of building step_valid3 from scratch via tape_update transfer,
    # use phase1_step_extend_trace which already handles ALL of this!
    # It builds the extended trace with Function, dom_bound, base_cond, step_valid.
    # I just need to provide the right inputs.
    #
    # phase1_step_extend_trace: ∀tra,ska,cn_new,c0,ka,delta,ca,w.
    #   Function(tra)→dom_bound(tra,ka)→Omega(w)→In(ka,w)→Succ(ska,ka)→
    #   base_cond(tra,c0)→step_valid(tra,ka)→TMStep(delta,ca,cn_new)→Apply(tra,ka,ca)→
    #   ∃trn. And(Function(trn), And(dom_bound(trn,ska), And(base_cond(trn,c0),
    #              And(Apply(trn,ska,cn_new), step_valid(trn,ska)))))
    #
    # I have Function(rn_tra), base_cond(rn_tra,x), step_valid(rn_tra,qn_pos), Apply(rn_tra,qn_pos,cj), TMStep(d,cj,ck1).
    # But extend_trace also needs dom_bound(rn_tra,qn_pos) which TMReaches doesn't have!
    # TMReaches now has Function but not dom_bound.
    #
    # Hmm. Without dom_bound, extend_trace can't work.
    # Can I derive dom_bound from the TMReaches trace?
    # dom_bound(tra,n) = ∀x,y. Apply(tra,x,y)→Or(In(x,n),Eq(x,n))
    # This says the trace's domain is bounded by n. TMReaches doesn't guarantee this.
    #
    # So I need EITHER:
    # 1. Add dom_bound to TMReaches. More invasive.
    # 2. Build step_valid3 directly (the 50+ line approach above).
    # 3. Find another way.
    #
    # Option 2 it is. But let me minimize the work by handling both cases (k∈qn_pos and k=qn_pos) efficiently.
    # For k∈qn_pos: sk=S(k). Not(Eq(k,spos)) because k∈qn_pos and spos=S(qn_pos). omega: k<qn_pos, spos=S(qn_pos)>qn_pos>k. So k≠spos.
    # For Not(Eq(sk,spos)): if S(k)=spos=S(qn_pos) then k=qn_pos by succ_injection. k∈qn_pos → k≠qn_pos (no-self). Contradiction.
    # For k=qn_pos: sk=S(qn_pos)=spos. Apply(tra3,qn_pos,ck_v) → Apply(rn_tra,qn_pos,ck_v) (tape_update_other_rev, qn_pos≠spos).
    #   func_unique(rn_tra): Apply(rn_tra,qn_pos,ck_v) ∧ Apply(rn_tra,qn_pos,cj) → Eq(ck_v,cj).
    #   rn_reached: Apply(rn_tra,qn_pos,cj) [actually it's Apply(rn_tra,qn_pos,qn_cj)].
    #   Wait: rn_reached is Apply(rn_tra,pos_j,cj) — the TMReaches's reached component. pos_j=qn_pos, cj=qn_cj. ✓
    #   TMStep(d,ck_v,ck1) → TMStep(d,cj,ck1) via... actually TMStep is ∀-quantified over internal vars.
    #   If ck_v=cj (from func_unique), then TMStep(d,ck_v,ck1)=TMStep(d,cj,ck1). ✓
    #   Actually we need ∃sv_ck1.And(Apply(tra3,sk,sv_ck1),TMStep(d,sv_ck,sv_ck1)).
    #   sk=spos. Apply(tra3,spos,ck1_var) from tape_update_at. sv_ck1=ck1_var.
    #   TMStep(d,sv_ck,ck1_var): need TMStep(d,ck_v,ck1_var). We have TMStep(d,qn_cj,ck1_var) from step2.
    #   With Eq(ck_v,cj): TMStep is a formula. Eq(ck_v,cj) allows substitution... no, TMStep is ∀-closed.
    #   TMStep(d,ck_v,ck1_var) needs to be DERIVED, not substituted.
    #   TMStep(d,qn_cj,ck1_var): for ALL decompositions of qn_cj, the step applies.
    #   TMStep(d,ck_v,ck1_var): for ALL decompositions of ck_v, the step applies.
    #   With Eq(ck_v,qn_cj): these are the SAME formula (via eq_transfer on TMStep).
    #   TMStep.subst(qn_cj,ck_v) gives TMStep(d,ck_v,ck1_var). Then Eq(ck_v,qn_cj) allows transfer.
    #   Actually TMStep(d,c1,c2) = ∀q,h,t,... TMConfig(c1,q,h,t)→... Eq(ck_v,qn_cj) transfers TMConfig.
    #   This is doable via config_eq_transfer or Eq transfer on the first arg of TMStep.
    #
    # This is feasible but LONG. Given the session, let me just add dom_bound to TMReaches too.
    # It's one more conjunct, similar to adding Function.
    print('compose step: step_valid3 requires dom_bound or complex omega ordering')
    print('Adding dom_bound to TMReaches would simplify, allowing phase1_step_extend_trace reuse')
    assert False, 'TODO: decide between dom_bound in TMReaches or inline step_valid3'


if __name__=='__main__':
    tmreaches_compose()
