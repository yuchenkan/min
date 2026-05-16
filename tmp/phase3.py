"""Phase3P proof — omega induction scanning past b ones in second group.

Like Phase1P but head starts at sa, position tracked via Plus(sa,j,pos_j).
Tape read via Phase3P's hypothesis: ∀p∈b.∀pp.Plus(sa,p,pp)→Apply(tape2,pp,one).
Same transition as Phase1P: q1,one→one,one(right),q1.
"""
import sys; sys.path.insert(0, '/root/min/src')
from core.lang import Var, In, Not, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq
from core.proof import Proof, Sequent, same
from vocab.ordpair import OrdPair, Successor
from vocab.omega import Omega, Num
from vocab.sets import Empty
from vocab.tm import TMConfig, TMTransition, TMStep, TMReaches
from vocab.functions import Function as FuncDef, Apply
from vocab.recursion import Plus as PlusDef
from tm import UnaryTape
from tactics import apply_thm, mp, ax, fl, eir, eel, cut, wl, wr, weaken_to
from theorems.logic import (and_intro, and_elim_left, and_elim_right,
    or_intro_left, or_intro_right, or_elim,
    eq_reflexive, eq_symmetric, iff_mp, iff_mp_rev, unique_empty, eq_substitution)
from theorems.sets import (eq_transfer, ordpair_exists, singleton_exists,
    omega_transitive_set as ots_fn)
from theorems.omega import omega_contains_empty, omega_succ_closed
from theorems.tm import (Phase3P, phase1_step_tmstep, phase1_step_extend_trace,
    config_exists)
from theorems.recursion import singleton_is_function, singleton_apply_eq, eq_apply_transfer
from theorems.arithmetic import plus_zero_exists, plus_succ_right, plus_val_in_omega
import core.zfc as zfc


class Phase3Ind:
    """Strong induction predicate for Phase3 trace construction.
    Phase3Ind(n, d, q1, sa, tape2, c1) =
      ∃pos_n. Plus(sa,n,pos_n) ∧
      ∃trace,cn. Function(trace) ∧ dom_bound(trace,n) ∧ base_cond(trace,c1) ∧
                 TMConfig(cn,q1,pos_n,tape2) ∧ Apply(trace,n,cn) ∧ step_valid(trace,n,d)"""
    __match_args__ = ('n','d','q1','sa','tape2','c1')
    def __init__(self, n, d, q1, sa, tape2, c1):
        self.n=n;self.d=d;self.q1=q1;self.sa=sa;self.tape2=tape2;self.c1=c1
    def expand(self):
        pos_n=Var(postfix='_pn');tra=Var(postfix='_tra');cn=Var(postfix='_cn')
        k=Var(postfix='_k');sk=Var(postfix='_sk');ck=Var(postfix='_ck');ck1=Var(postfix='_ck1')
        zp=Var(postfix='_zp');xd=Var(postfix='_xd');yd=Var(postfix='_yd')
        base_cond=Forall(zp,Implies(Empty(zp),Apply(tra,zp,self.c1)))
        dom_bound=Forall(xd,Forall(yd,Implies(Apply(tra,xd,yd),Or(In(xd,self.n),Eq(xd,self.n)))))
        step_valid=Forall(k,Implies(In(k,self.n),Forall(sk,Implies(Successor(sk,k),
            Forall(ck,Implies(Apply(tra,k,ck),Exists(ck1,And(Apply(tra,sk,ck1),TMStep(self.d,ck,ck1)))))))))
        inner=Exists(tra,Exists(cn,And(FuncDef(tra),And(dom_bound,And(base_cond,
            And(TMConfig(cn,self.q1,pos_n,self.tape2),And(Apply(tra,self.n,cn),step_valid)))))))
        return Exists(pos_n,And(PlusDef(self.sa,self.n,pos_n),inner))
    def subst(self,old,new):
        r=lambda f:new if f is old else f
        return Phase3Ind(r(self.n),r(self.d),r(self.q1),r(self.sa),r(self.tape2),r(self.c1))
    def __str__(self):
        return f'P3Ind({self.n})'


if __name__=='__main__':
    d=Var(postfix='d');q1=Var(postfix='q1');sa=Var(postfix='sa')
    tape2=Var(postfix='t2');c1=Var(postfix='c1');z=Var(postfix='z');n=Var(postfix='n')
    p=Phase3Ind(z,d,q1,sa,tape2,c1)
    print(f'Phase3Ind(z,...): {p}')
    print(f'  expand: {str(p.expand())[:120]}')
    print(f'  same(self,self)? {same(p,p)}')


def phase3_base():
    """Pairing |- ∀d,q1,sa,tape2,c1,z,w.
        Num(z,0) → Omega(w) → In(sa,w) →
        TMConfig(c1,q1,sa,tape2) → Phase3Ind(z,d,q1,sa,tape2,c1)"""
    from core.proof import Proof, Sequent, same, _subst
    from vocab.sets import Singleton

    def mk_and(gl,gr):
        L,R=gl.sequent.right[0],gr.sequent.right[0]
        return mp(apply_thm(and_intro(L,R,[]),[],L,Implies(R,And(L,R)),gl),gr,R,And(L,R))

    d=Var(postfix='d');q1=Var(postfix='q1');sa=Var(postfix='sa')
    tape2=Var(postfix='t2');c1=Var(postfix='c1');z=Var(postfix='z');w=Var(postfix='w')
    num_z=Num(z,0);omega_w=Omega(w);in_sa_w=In(sa,w)
    cfg_c1=TMConfig(c1,q1,sa,tape2)
    goal=Phase3Ind(z,d,q1,sa,tape2,c1)

    # Plus(sa,z,sa) from plus_zero_exists
    _pze=plus_zero_exists()
    got_plus=apply_thm(_pze,[w,sa,z])
    got_plus=mp(got_plus,ax(omega_w),omega_w,got_plus.sequent.right[0].right)
    got_plus=mp(got_plus,ax(in_sa_w),in_sa_w,got_plus.sequent.right[0].right)
    got_plus=mp(got_plus,ax(num_z),num_z,got_plus.sequent.right[0].right)
    # |- Plus(sa,z,sa)

    # Singleton trace {z→c1} — same as phase1_base
    pair_zc1=Var(postfix='pzc');t_sing=Var(postfix='ts')
    op_pair=OrdPair(pair_zc1,z,c1);sing_t=Singleton(t_sing,pair_zc1)
    got_ex_pair=apply_thm(ordpair_exists(),[z,c1],concl=Exists(pair_zc1,op_pair))
    sif=singleton_is_function()
    got_func_s=apply_thm(sif,[pair_zc1,z,c1,t_sing])
    got_func_s=mp(got_func_s,ax(op_pair),op_pair,got_func_s.sequent.right[0].right)
    got_func_s=mp(got_func_s,ax(sing_t),sing_t,FuncDef(t_sing))
    # Apply(t_sing,z,c1)
    iff_is=Iff(In(pair_zc1,t_sing),Eq(pair_zc1,pair_zc1))
    got_iff_s=apply_thm(ax(sing_t),[pair_zc1],concl=iff_is)
    got_epp=apply_thm(eq_reflexive(),[pair_zc1])
    got_inp=mp(apply_thm(iff_mp_rev(In(pair_zc1,t_sing),Eq(pair_zc1,pair_zc1),[]),[],
        iff_is,Implies(Eq(pair_zc1,pair_zc1),In(pair_zc1,t_sing)),got_iff_s),
        got_epp,Eq(pair_zc1,pair_zc1),In(pair_zc1,t_sing))
    got_app_s=eir(mk_and(ax(op_pair),got_inp),And(op_pair,In(pair_zc1,t_sing)),pair_zc1,pair_zc1)
    # base_cond, dom_bound, step_valid — identical to phase1_base
    zp=Var(postfix='_zp');ue=unique_empty();es=eq_symmetric();eat=eq_apply_transfer()
    got_ezz=apply_thm(ue,[zp],Empty(zp),Forall(z,Implies(num_z,Eq(zp,z))),ax(Empty(zp)))
    got_ezz=apply_thm(got_ezz,[z],num_z,Eq(zp,z),ax(num_z))
    got_ezzp=apply_thm(es,[zp,z],Eq(zp,z),Eq(z,zp),got_ezz)
    got_azp=apply_thm(eat,[t_sing,z,zp,c1])
    got_azp=mp(got_azp,got_ezzp,Eq(z,zp),Implies(Apply(t_sing,z,c1),Apply(t_sing,zp,c1)))
    got_azp=mp(got_azp,got_app_s,Apply(t_sing,z,c1),Apply(t_sing,zp,c1))
    imp_bc=Implies(Empty(zp),Apply(t_sing,zp,c1))
    lbc=[f for f in got_azp.sequent.left if not same(f,Empty(zp))]
    got_bc=Proof(Sequent(lbc,[imp_bc]),'implies_right',[got_azp],principal=imp_bc)
    got_bc=Proof(Sequent(got_bc.sequent.left,[Forall(zp,imp_bc)]),'forall_right',[got_bc],principal=Forall(zp,imp_bc),term=zp)
    # dom_bound
    xd=Var(postfix='_xd');yd=Var(postfix='_yd');sae=singleton_apply_eq()
    got_sae=apply_thm(sae,[z,c1,pair_zc1,t_sing,xd,yd])
    got_sae=mp(got_sae,ax(op_pair),op_pair,got_sae.sequent.right[0].right)
    got_sae=mp(got_sae,ax(sing_t),sing_t,got_sae.sequent.right[0].right)
    got_sae=mp(got_sae,ax(Apply(t_sing,xd,yd)),Apply(t_sing,xd,yd),got_sae.sequent.right[0].right)
    got_ezxd=apply_thm(and_elim_left(Eq(z,xd),Eq(c1,yd),[]),[],got_sae.sequent.right[0],Eq(z,xd),got_sae)
    got_exdz=apply_thm(es,[z,xd],Eq(z,xd),Eq(xd,z),got_ezxd)
    or_xdz=Or(In(xd,z),Eq(xd,z))
    got_orx=apply_thm(or_intro_right(In(xd,z),Eq(xd,z),[]),[],Eq(xd,z),or_xdz,got_exdz)
    imp_db=Implies(Apply(t_sing,xd,yd),or_xdz)
    ldb=[f for f in got_orx.sequent.left if not same(f,Apply(t_sing,xd,yd))]
    got_db=Proof(Sequent(ldb,[imp_db]),'implies_right',[got_orx],principal=imp_db)
    got_db=Proof(Sequent(got_db.sequent.left,[Forall(yd,imp_db)]),'forall_right',[got_db],principal=Forall(yd,imp_db),term=yd)
    got_db=Proof(Sequent(got_db.sequent.left,[Forall(xd,Forall(yd,imp_db))]),'forall_right',[got_db],principal=Forall(xd,Forall(yd,imp_db)),term=xd)
    # step_valid — vacuous
    _k=Var(postfix='_k');_sk=Var(postfix='_sk');_ck=Var(postfix='_ck');_ck1=Var(postfix='_ck1')
    got_nkz=apply_thm(ax(num_z),[_k])
    sv_inner=Forall(_sk,Implies(Successor(_sk,_k),Forall(_ck,Implies(Apply(t_sing,_k,_ck),Exists(_ck1,And(Apply(t_sing,_sk,_ck1),TMStep(d,_ck,_ck1)))))))
    nkz=Not(In(_k,z));gb=Proof(Sequent([In(_k,z),nkz],[]),'not_left',[ax(In(_k,z))],principal=nkz)
    gb=Proof(Sequent(gb.sequent.left,[sv_inner]),'weakening_right',[gb],principal=sv_inner)
    gb=cut(gb,nkz,got_nkz);imp_sv=Implies(In(_k,z),sv_inner)
    lsv=[f for f in gb.sequent.left if not same(f,In(_k,z))]
    got_sv=Proof(Sequent(lsv,[imp_sv]),'implies_right',[gb],principal=imp_sv)
    got_sv=Proof(Sequent(got_sv.sequent.left,[Forall(_k,imp_sv)]),'forall_right',[got_sv],principal=Forall(_k,imp_sv),term=_k)

    # Assemble Phase3Ind(z,...) = ∃pos_n. And(Plus(sa,z,pos_n), ∃tra,cn.(...))
    # Inner: And(Function, And(dom_bound, And(base_cond, And(TMConfig(cn,q1,sa,tape2), And(Apply,step_valid)))))
    pza=mk_and(got_app_s,got_sv);pza=mk_and(ax(cfg_c1),pza);pza=mk_and(got_bc,pza)
    pza=mk_and(got_db,pza);pza=mk_and(got_func_s,pza)
    # eir cn=c1, tra=t_sing into inner ∃
    exp=goal.expand()
    pos_n_var=exp.var  # ∃pos_n
    and_plus_inner=exp.body  # And(Plus(sa,z,pos_n), inner_exists)
    inner_exists=and_plus_inner.right  # ∃tra.∃cn.(...)
    tra_var=inner_exists.var
    inner_cn=inner_exists.body  # ∃cn.(...)
    cn_var=inner_cn.var
    inner_and=inner_cn.body  # And(Function(tra),...)
    # eir cn=c1 (body needs tra→t_sing and pos_n→sa substituted)
    body_cn=_subst(_subst(inner_and,tra_var,t_sing),pos_n_var,sa)
    got_ecn=eir(pza,body_cn,cn_var,c1)
    # eir tra=t_sing (inner_cn with pos_n→sa)
    inner_cn_sa=_subst(inner_cn,pos_n_var,sa)
    got_etr=eir(got_ecn,inner_cn_sa,tra_var,t_sing)
    # eir pos_n=sa: And(Plus(sa,z,pos_n), inner_exists)
    got_and_plus=mk_and(got_plus,got_etr)
    got_epos=eir(got_and_plus,and_plus_inner,pos_n_var,sa)
    assert same(got_epos.sequent.right[0],goal),'Phase3Ind(z) mismatch'
    # eel singleton eigenvars
    se2=singleton_exists();got_es2=apply_thm(se2,[pair_zc1],concl=Exists(t_sing,sing_t))
    got_epos=eel(got_epos,sing_t,t_sing);got_epos=cut(got_epos,Exists(t_sing,sing_t),got_es2)
    got_epos=eel(got_epos,op_pair,pair_zc1);got_epos=cut(got_epos,Exists(pair_zc1,op_pair),got_ex_pair)
    # Discharge + close
    for hyp in [cfg_c1,in_sa_w,omega_w,num_z]:
        got_epos=wl(got_epos,hyp);imp=Implies(hyp,got_epos.sequent.right[0])
        left=[f for f in got_epos.sequent.left if not same(f,hyp)]
        got_epos=Proof(Sequent(left,[imp]),'implies_right',[got_epos],principal=imp)
    for v in [w,z,c1,tape2,sa,q1,d]:
        body=got_epos.sequent.right[0];fa=Forall(v,body)
        got_epos=Proof(Sequent(got_epos.sequent.left,[fa]),'forall_right',[got_epos],principal=fa,term=v)
    got_epos.name='phase3_base'
    return got_epos


def phase3_step_case():
    """ZFC |- ∀d,q1,sa,tape2,c1,n,sn,w,one,b.
        TMTransition(d,q1,one,one,one,q1) → Omega(w) → In(b,w) → In(sa,w) → In(n,w) →
        Function(d) → Function(tape2) → Num(one,1) →
        (∀p∈b.∀pp.Plus(sa,p,pp)→Apply(tape2,pp,one)) →
        Successor(sn,n) → In(n,b) →
        Phase3Ind(n,d,q1,sa,tape2,c1) → Phase3Ind(sn,d,q1,sa,tape2,c1)"""
    from core.proof import Proof, Sequent, same, _subst

    def mk_and(gl,gr):
        L,R=gl.sequent.right[0],gr.sequent.right[0]
        return mp(apply_thm(and_intro(L,R,[]),[],L,Implies(R,And(L,R)),gl),gr,R,And(L,R))

    d=Var(postfix='d');q1=Var(postfix='q1');sa=Var(postfix='sa')
    tape2=Var(postfix='t2');c1=Var(postfix='c1')
    n=Var(postfix='n');sn=Var(postfix='sn');w=Var(postfix='w');one=Var(postfix='one')
    b=Var(postfix='b')
    trans=TMTransition(d,q1,one,one,one,q1)
    omega_w=Omega(w);in_b_w=In(b,w);in_sa_w=In(sa,w);in_n_w=In(n,w)
    func_d=FuncDef(d);func_tape2=FuncDef(tape2);num_one=Num(one,1)
    succ_sn=Successor(sn,n)
    pn=Phase3Ind(n,d,q1,sa,tape2,c1);psn=Phase3Ind(sn,d,q1,sa,tape2,c1)

    # tape_read hypothesis: ∀p∈b.∀pp.Plus(sa,p,pp)→Apply(tape2,pp,one)
    p_var=Var(postfix='_p');pp_var=Var(postfix='_pp')
    tape_read=Forall(p_var,Implies(In(p_var,b),Forall(pp_var,Implies(PlusDef(sa,p_var,pp_var),Apply(tape2,pp_var,one)))))

    # Open Phase3Ind(n,...): ∃pos_n.And(Plus(sa,n,pos_n), ∃tra,cn.(...))
    pn_exp=pn.expand();pos_n_var=pn_exp.var;pn_body=pn_exp.body
    # pn_body = And(Plus(sa,n,pos_n), inner_exists)
    plus_sa_n=pn_body.left  # Plus(sa,n,pos_n_var)
    inner_exists=pn_body.right  # ∃tra.∃cn.(...)
    tra_var=inner_exists.var
    inner_cn=inner_exists.body  # ∃cn.(And(Function,...))
    cn_var=inner_cn.var
    inner_and=inner_cn.body

    # Decompose inner_and
    b0=inner_and
    gft=apply_thm(and_elim_left(b0.left,b0.right,[]),[],b0,b0.left,ax(b0))
    b1=b0.right;gb1=apply_thm(and_elim_right(b0.left,b1,[]),[],b0,b1,ax(b0))
    gdb=apply_thm(and_elim_left(b1.left,b1.right,[]),[],b1,b1.left,gb1)
    b2=b1.right;gb2=apply_thm(and_elim_right(b1.left,b2,[]),[],b1,b2,gb1)
    gbt=apply_thm(and_elim_left(b2.left,b2.right,[]),[],b2,b2.left,gb2)
    b3=b2.right;gb3=apply_thm(and_elim_right(b2.left,b3,[]),[],b2,b3,gb2)
    gcn=apply_thm(and_elim_left(b3.left,b3.right,[]),[],b3,b3.left,gb3)
    b4=b3.right;gb4=apply_thm(and_elim_right(b3.left,b4,[]),[],b3,b4,gb3)
    gatn=apply_thm(and_elim_left(b4.left,b4.right,[]),[],b4,b4.left,gb4)
    gsvn=apply_thm(and_elim_right(b4.left,b4.right,[]),[],b4,b4.right,gb4)
    # Also extract Plus(sa,n,pos_n) from pn_body
    got_plus_n=apply_thm(and_elim_left(plus_sa_n,inner_exists,[]),[],pn_body,plus_sa_n,ax(pn_body))

    # tape_read at position pos_n: In(n,b) → Plus(sa,n,pos_n) → Apply(tape2,pos_n,one)
    got_tr=apply_thm(ax(tape_read),[n])
    cur=got_tr.sequent.right[0]
    got_tr=mp(got_tr,ax(In(n,b)),cur.left,cur.right)
    got_tr=apply_thm(got_tr,[pos_n_var])
    cur=got_tr.sequent.right[0]
    got_tr=mp(got_tr,got_plus_n,cur.left,cur.right)
    # [tape_read, In(n,b), pn_body, inner_and] |- Apply(tape2,pos_n,one)
    got_app_pos=got_tr
    print('phase3 step: Apply(tape2,pos_n,one) done')

    # phase1_step_tmstep: builds TMStep for q1,one→one,right,q1
    # Same transition as Phase1P! d1=one.
    _pst=phase1_step_tmstep()
    got_tmstep=apply_thm(_pst,[d,q1,pos_n_var,sn,tape2,cn_var,one,one])
    # Order: Function(d)→TMTransition→TMConfig(cn,q1,pos_n,tape2)→Function(tape2)→Apply(tape2,pos_n,one)→Num(one,1)→Succ(sn,pos_n)
    # Wait — phase1_step_tmstep's Successor is Succ(ska,ka) where ska=sn and ka=pos_n.
    # But Succ(sn,pos_n) is NOT Succ(sn,n)! sn=S(n), not S(pos_n).
    # I need Succ(s_pos, pos_n) where s_pos = pos_n + 1 = sa + n + 1 = sa + sn.
    # From Plus(sa,n,pos_n) + Succ(sn,n): Plus(sa,sn,s_pos) via plus_succ_right.
    # And Succ(s_pos, pos_n) from the Plus step.
    # But phase1_step_tmstep expects Successor(ska,ka) where ska is the new head position.
    # The new head = pos_n + 1 = S(pos_n). I need a Successor(s_pos, pos_n) where
    # s_pos is the new position. And Plus(sa,sn,s_pos) for Phase3Ind(sn,...).
    #
    # Let me use successor_exists to get ∃s_pos. Succ(s_pos,pos_n).
    from theorems.sets import successor_exists
    s_pos=Var(postfix='sp')
    succ_sp=Successor(s_pos,pos_n_var)
    got_ex_sp=apply_thm(successor_exists(),[pos_n_var],concl=Exists(s_pos,succ_sp))

    got_tmstep=apply_thm(_pst,[d,q1,pos_n_var,s_pos,tape2,cn_var,one,one])
    got_tmstep=mp(got_tmstep,ax(func_d),func_d,got_tmstep.sequent.right[0].right)
    got_tmstep=mp(got_tmstep,ax(trans),trans,got_tmstep.sequent.right[0].right)
    got_tmstep=mp(got_tmstep,gcn,gcn.sequent.right[0],got_tmstep.sequent.right[0].right)
    got_tmstep=mp(got_tmstep,ax(func_tape2),func_tape2,got_tmstep.sequent.right[0].right)
    got_tmstep=mp(got_tmstep,got_app_pos,Apply(tape2,pos_n_var,one),got_tmstep.sequent.right[0].right)
    got_tmstep=mp(got_tmstep,ax(num_one),num_one,got_tmstep.sequent.right[0].right)
    got_tmstep=mp(got_tmstep,ax(succ_sp),succ_sp,got_tmstep.sequent.right[0].right)
    # ∃cn_new. And(TMConfig(cn_new,q1,s_pos,tape2), TMStep(d,cn_var,cn_new))
    print('phase3 step: tmstep done')

    # Derive Plus(sa,sn,s_pos) from Plus(sa,n,pos_n) + Succ(sn,n) + Succ(s_pos,pos_n)
    # plus_succ_right: ∀w,m,n,p,sn,sp. Omega→In(m,w)→In(n,w)→Plus(m,n,p)→Succ(sn,n)→Succ(sp,p)→Plus(m,sn,sp)
    _psr=plus_succ_right()
    got_plus_sn=apply_thm(_psr,[w,sa,n,pos_n_var,sn,s_pos])
    got_plus_sn=mp(got_plus_sn,ax(omega_w),omega_w,got_plus_sn.sequent.right[0].right)
    got_plus_sn=mp(got_plus_sn,ax(in_sa_w),in_sa_w,got_plus_sn.sequent.right[0].right)
    got_plus_sn=mp(got_plus_sn,ax(in_n_w),in_n_w,got_plus_sn.sequent.right[0].right)
    got_plus_sn=mp(got_plus_sn,got_plus_n,plus_sa_n,got_plus_sn.sequent.right[0].right)
    got_plus_sn=mp(got_plus_sn,ax(succ_sn),succ_sn,got_plus_sn.sequent.right[0].right)
    got_plus_sn=mp(got_plus_sn,ax(succ_sp),succ_sp,got_plus_sn.sequent.right[0].right)
    # |- Plus(sa,sn,s_pos)
    print('phase3 step: Plus(sa,sn,s_pos) done')

    # phase1_step_extend_trace
    _pet=phase1_step_extend_trace()
    tsx=got_tmstep.sequent.right[0];cnw=tsx.var;tsb=tsx.body
    gcfn=apply_thm(and_elim_left(tsb.left,tsb.right,[]),[],tsb,tsb.left,ax(tsb))
    gstn=apply_thm(and_elim_right(tsb.left,tsb.right,[]),[],tsb,tsb.right,ax(tsb))
    gext=apply_thm(_pet,[tra_var,sn,cnw,c1,n,d,cn_var,w])
    gext=mp(gext,gft,gft.sequent.right[0],gext.sequent.right[0].right)
    gext=mp(gext,gdb,gdb.sequent.right[0],gext.sequent.right[0].right)
    gext=mp(gext,ax(omega_w),omega_w,gext.sequent.right[0].right)
    gext=mp(gext,ax(in_n_w),in_n_w,gext.sequent.right[0].right)
    gext=mp(gext,ax(succ_sn),succ_sn,gext.sequent.right[0].right)
    gext=mp(gext,gbt,gbt.sequent.right[0],gext.sequent.right[0].right)
    gext=mp(gext,gsvn,gsvn.sequent.right[0],gext.sequent.right[0].right)
    gext=mp(gext,gstn,gstn.sequent.right[0],gext.sequent.right[0].right)
    gext=mp(gext,gatn,gatn.sequent.right[0],gext.sequent.right[0].right)
    print('phase3 step: extend_trace done')

    # Decompose extended trace, insert TMConfig(cnw,...) and Plus, build Phase3Ind(sn,...)
    extx=gext.sequent.right[0];trn=extx.var;extb=extx.body
    e0=extb
    gef=apply_thm(and_elim_left(e0.left,e0.right,[]),[],e0,e0.left,ax(e0))
    e1=e0.right;ge1=apply_thm(and_elim_right(e0.left,e1,[]),[],e0,e1,ax(e0))
    gedb=apply_thm(and_elim_left(e1.left,e1.right,[]),[],e1,e1.left,ge1)
    e2=e1.right;ge2=apply_thm(and_elim_right(e1.left,e2,[]),[],e1,e2,ge1)
    gebc=apply_thm(and_elim_left(e2.left,e2.right,[]),[],e2,e2.left,ge2)
    e3=e2.right;ge3=apply_thm(and_elim_right(e2.left,e3,[]),[],e2,e3,ge2)
    geap=apply_thm(and_elim_left(e3.left,e3.right,[]),[],e3,e3.left,ge3)
    gesv=apply_thm(and_elim_right(e3.left,e3.right,[]),[],e3,e3.right,ge3)

    # Reassemble with TMConfig(cnw,q1,s_pos,tape2) from tmstep
    psna=mk_and(geap,gesv);psna=mk_and(gcfn,psna);psna=mk_and(gebc,psna)
    psna=mk_and(gedb,psna);psna=mk_and(gef,psna)

    # eir into Phase3Ind(sn,...) structure: ∃pos_sn. And(Plus(sa,sn,pos_sn), ∃tra.∃cn.(...))
    psn_exp=psn.expand();psn_pos=psn_exp.var;psn_body=psn_exp.body
    psn_plus=psn_body.left;psn_inner=psn_body.right
    psn_tra=psn_inner.var;psn_cn_ex=psn_inner.body
    psn_cn=psn_cn_ex.var;psn_and=psn_cn_ex.body

    # eir cn=cnw, tra=trn (substituting pos_sn→s_pos in body)
    from core.proof import _subst
    body_cn=_subst(_subst(psn_and,psn_tra,trn),psn_pos,s_pos)
    got_ecn=eir(psna,body_cn,psn_cn,cnw)
    inner_cn_sp=_subst(psn_cn_ex,psn_pos,s_pos)
    got_etr=eir(got_ecn,inner_cn_sp,psn_tra,trn)
    # And with Plus(sa,sn,s_pos)
    got_and_plus=mk_and(got_plus_sn,got_etr)
    got_epos=eir(got_and_plus,psn_body,psn_pos,s_pos)
    assert same(got_epos.sequent.right[0],psn),'Phase3Ind(sn) mismatch'
    print('phase3 step: Phase3Ind(sn) assembled')

    # eel eigenvars: trn from extb, cnw from tsb, s_pos from succ_sp,
    # cn_var and tra_var from inner_and, pos_n_var from pn_body
    got_epos=eel(got_epos,extb,trn);got_epos=cut(got_epos,extx,gext)
    got_epos=eel(got_epos,tsb,cnw);got_epos=cut(got_epos,tsx,got_tmstep)
    got_epos=eel(got_epos,succ_sp,s_pos);got_epos=cut(got_epos,Exists(s_pos,succ_sp),got_ex_sp)
    # eel cn_var, tra_var, pos_n_var — reform pn_body then pn_exp, cut with ax(pn)
    got_epos=eel(got_epos,inner_and,cn_var)
    # left now has Exists(cn_var,inner_and)=inner_cn instead of inner_and. eel tra_var:
    got_epos=eel(got_epos,inner_cn,tra_var)
    # left now has Exists(tra_var,inner_cn)=inner_exists. Combine with plus into pn_body:
    # pn_body=And(plus_sa_n,inner_exists). Both are on the left.
    # Actually inner_exists was produced by eel — it replaced inner_cn.
    # And plus_sa_n came from ax(pn_body) decomposition — pn_body is still on left too.
    # pn_body has pos_n_var free. inner_exists (from eel) also has pos_n_var free.
    # But plus_sa_n (from and_elim_left on pn_body) also has pn_body on its left.
    # The issue: after all the cuts and eels, pn_body is on the left (from the original ax).
    # inner_exists is ALSO on the left (from the eel of tra_var).
    # Both have pos_n_var. I need to cut inner_exists with something to remove it.
    # inner_exists is a sub-formula of pn_body. So if I eel pos_n_var from pn_body,
    # inner_exists (separately on left) would block it.
    # Fix: combine them. inner_exists on left came from eel(inner_cn, tra_var).
    # The eel replaced inner_cn with Exists(tra_var, inner_cn) = inner_exists.
    # Before that, inner_cn came from eel(inner_and, cn_var).
    # Before that, inner_and came from ax(pn_body) decomposition.
    # So the chain is: pn_body → inner_and (via And decomposition) → inner_cn (eel cn) → inner_exists (eel tra).
    # All of these put pn_body on their left via ax(pn_body).
    # So pn_body IS on the left, AND inner_exists IS on the left.
    # The inner_exists is REDUNDANT (it's contained in pn_body).
    # Cut it: inner_exists on left is same as pn_body.right (And_elim_right).
    # Or simpler: just cut inner_exists with and_elim_right from pn_body.
    got_inner_from_pn = apply_thm(and_elim_right(plus_sa_n,inner_exists,[]),[],pn_body,inner_exists,ax(pn_body))
    got_epos = cut(got_epos, inner_exists, got_inner_from_pn)
    # Now only pn_body has pos_n_var on left. eel it.
    got_epos=eel(got_epos,pn_body,pos_n_var)
    got_epos=cut(got_epos,pn_exp,ax(pn))
    print('phase3 step: eigenvars cleaned')

    # Discharge + ∀-close
    hyps=[pn,In(n,b),succ_sn,num_one,tape_read,func_tape2,func_d,in_n_w,in_sa_w,in_b_w,omega_w,trans]
    for hyp in hyps:
        got_epos=wl(got_epos,hyp);imp=Implies(hyp,got_epos.sequent.right[0])
        left=[f for f in got_epos.sequent.left if not same(f,hyp)]
        got_epos=Proof(Sequent(left,[imp]),'implies_right',[got_epos],principal=imp)
    for v in [one,w,b,sn,n,c1,tape2,sa,q1,d]:
        body=got_epos.sequent.right[0];fa=Forall(v,body)
        got_epos=Proof(Sequent(got_epos.sequent.left,[fa]),'forall_right',[got_epos],principal=fa,term=v)
    got_epos.name='phase3_step_case'
    return got_epos


def phase3():
    """ZFC |- Phase3P(). Omega induction using phase3_base + phase3_step_case."""
    from core.proof import Proof,Sequent,same,_var_free_in_sequent,_subst
    from theorems.omega import omega_smallest_inductive,omega_contains_empty,omega_succ_closed
    from theorems.tm import Phase3P,config_eq
    from theorems.recursion import eq_apply_val_transfer
    from theorems.sets import ordpair_exists as _oe_fn,ordpair_unique as _ou_fn
    from vocab.sets import TransitiveSet
    import core.zfc as zfc

    def mk_and(gl,gr):
        L,R=gl.sequent.right[0],gr.sequent.right[0]
        return mp(apply_thm(and_intro(L,R,[]),[],L,Implies(R,And(L,R)),gl),gr,R,And(L,R))

    d=Var(postfix='d');q1=Var(postfix='q1');sa=Var(postfix='sa')
    b=Var(postfix='b');pos=Var(postfix='pos');tape2=Var(postfix='t2')
    c1v=Var(postfix='c1');c2v=Var(postfix='c2');w=Var(postfix='w');one=Var(postfix='one')
    z=Var(postfix='z');n=Var(postfix='ind_n');sn=Var(postfix='ind_sn')
    pv=Var(postfix='ind_pv');xv=Var(postfix='ind_xv')
    trans=TMTransition(d,q1,one,one,one,q1);omega_w=Omega(w)
    in_b_w=In(b,w);in_sa_w=In(sa,w);func_d=FuncDef(d);func_tape2=FuncDef(tape2)
    num_one=Num(one,1);num_z=Num(z,0)
    p_var=Var(postfix='_p');pp_var=Var(postfix='_pp')
    tape_read=Forall(p_var,Implies(In(p_var,b),Forall(pp_var,Implies(PlusDef(sa,p_var,pp_var),Apply(tape2,pp_var,one)))))
    plus_sab=PlusDef(sa,b,pos);cfg_c1=TMConfig(c1v,q1,sa,tape2);cfg_c2=TMConfig(c2v,q1,pos,tape2)
    succ_sn=Successor(sn,n)
    pind_n=Phase3Ind(n,d,q1,sa,tape2,c1v)

    def Q(nn): return Implies(Or(In(nn,b),Eq(nn,b)),Phase3Ind(nn,d,q1,sa,tape2,c1v))

    # === Separation ===
    sep=zfc.Separation(Q,[b,d,q1,sa,tape2,c1v])
    sep_ax=Proof(Sequent([sep],[sep]),'axiom',principal=sep)
    char_pv=Forall(xv,Iff(In(xv,pv),And(In(xv,w),Q(xv))))
    got_ex_pv=apply_thm(sep_ax,[c1v,tape2,sa,q1,d,b,w],concl=Exists(pv,char_pv))
    def char_bwd(term,got_in_w,got_Q):
        gi=apply_thm(ax(char_pv),[term]);ii=gi.sequent.right[0];af=ii.right
        gr=apply_thm(iff_mp_rev(ii.left,ii.right,[]),[],ii,Implies(af,ii.left),gi)
        ai2=and_intro(af.left,af.right,[]);ga=apply_thm(ai2,[],af.left,Implies(af.right,af),got_in_w)
        gand=mp(ga,got_Q,af.right,af);return mp(gr,gand,af,ii.left)
    def char_fwd(term):
        gi=apply_thm(ax(char_pv),[term]);ii=gi.sequent.right[0]
        gimp=apply_thm(iff_mp(ii.left,ii.right,[]),[],ii,Implies(ii.left,ii.right),gi)
        return mp(gimp,ax(In(term,pv)),In(term,pv),ii.right)
    print('phase3: sep done')

    # === BASE ===
    oce=omega_contains_empty()
    got_z_w=apply_thm(oce,[w],omega_w,Forall(z,Implies(num_z,In(z,w))),ax(omega_w))
    got_z_w=apply_thm(got_z_w,[z],num_z,In(z,w),ax(num_z))
    _pb=phase3_base()
    got_pb=apply_thm(_pb,[d,q1,sa,tape2,c1v,z,w])
    got_pb=mp(got_pb,ax(num_z),num_z,got_pb.sequent.right[0].right)
    got_pb=mp(got_pb,ax(omega_w),omega_w,got_pb.sequent.right[0].right)
    got_pb=mp(got_pb,ax(in_sa_w),in_sa_w,got_pb.sequent.right[0].right)
    got_pb=mp(got_pb,ax(cfg_c1),cfg_c1,got_pb.sequent.right[0].right)
    or_zb=Or(In(z,b),Eq(z,b))
    got_Qz=wl(got_pb,or_zb);imp_qz=Implies(or_zb,got_Qz.sequent.right[0])
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
    print('phase3: ind_base done')

    # === STEP ===
    got_an=char_fwd(n)
    got_in_nw=apply_thm(and_elim_left(In(n,w),Q(n),[]),[],got_an.sequent.right[0],In(n,w),got_an)
    got_Qn=apply_thm(and_elim_right(In(n,w),Q(n),[]),[],got_an.sequent.right[0],Q(n),got_an)
    osc=omega_succ_closed()
    got_snw=apply_thm(osc,[w],omega_w,Forall(n,Implies(In(n,w),Forall(sn,Implies(succ_sn,In(sn,w))))),ax(omega_w))
    got_snw=apply_thm(got_snw,[n],In(n,w),Forall(sn,Implies(succ_sn,In(sn,w))),got_in_nw)
    got_snw=apply_thm(got_snw,[sn],succ_sn,In(sn,w),ax(succ_sn))
    # In(n,b) from Or(In(sn,b),Eq(sn,b)) via TransitiveSet(b)
    or_snb=Or(In(sn,b),Eq(sn,b))
    or_nsn=Or(In(n,n),Eq(n,n))
    iff_nsn=Iff(In(n,sn),or_nsn)
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
    # Q(n)→P(n)
    or_nb=Or(In(n,b),Eq(n,b))
    got_ornb=apply_thm(or_intro_left(In(n,b),Eq(n,b),[]),[],In(n,b),or_nb,got_inb)
    got_Pn=mp(got_Qn,got_ornb,or_nb,pind_n)
    # phase3_step_case
    _psc=phase3_step_case()
    got_psc=apply_thm(_psc,[d,q1,sa,tape2,c1v,n,sn,b,w,one])
    # Order from step_case: trans,omega,In(b,w),In(sa,w),In(n,w),func_d,func_tape2,num_one,tape_read,succ_sn,In(n,b),Phase3Ind(n,...)
    got_psc=mp(got_psc,ax(trans),trans,got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,ax(omega_w),omega_w,got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,ax(in_b_w),in_b_w,got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,ax(in_sa_w),in_sa_w,got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,got_in_nw,In(n,w),got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,ax(func_d),func_d,got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,ax(func_tape2),func_tape2,got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,ax(tape_read),tape_read,got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,ax(num_one),num_one,got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,ax(succ_sn),succ_sn,got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,got_inb,In(n,b),got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,got_Pn,pind_n,got_psc.sequent.right[0].right)
    pind_sn=Phase3Ind(sn,d,q1,sa,tape2,c1v)
    imp_qsn=Implies(or_snb,pind_sn)
    lqsn=[f for f in wl(got_psc,or_snb).sequent.left if not same(f,or_snb)]
    got_Qsn=Proof(Sequent(lqsn,[imp_qsn]),'implies_right',[wl(got_psc,or_snb)],principal=imp_qsn)
    got_step_pv=char_bwd(sn,got_snw,got_Qsn)
    if any(same(In(n,w),f) for f in got_step_pv.sequent.left):
        got_step_pv=cut(got_step_pv,In(n,w),got_in_nw)
    print('phase3: step In(sn,pv) done')

    # Discharge sn,n
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
    print('phase3: ind_step done')

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
    for h in [f_ for f_ in got_osi.sequent.left if not isinstance(f_,zfc.ZFCAxiom) and not same(f_,omega_w)]:
        got_osi=cut(got_osi,h,gas)
    print('phase3: osi done')

    # === Extract Q(b) → Phase3Ind(b,...) ===
    iff_bpv=Iff(In(b,pv),In(b,w))
    got_iff_b=cut(fl(eq_pw,iff_bpv,b),eq_pw,got_osi)
    got_bpv=mp(apply_thm(iff_mp_rev(In(b,pv),In(b,w),[]),[],iff_bpv,Implies(In(b,w),In(b,pv)),got_iff_b),ax(in_b_w),in_b_w,In(b,pv))
    got_andb=cut(char_fwd(b),In(b,pv),got_bpv)
    got_Qb=apply_thm(and_elim_right(In(b,w),Q(b),[]),[],got_andb.sequent.right[0],Q(b),got_andb)
    or_bb=Or(In(b,b),Eq(b,b));got_orbb=apply_thm(or_intro_right(In(b,b),Eq(b,b),[]),[],Eq(b,b),or_bb,apply_thm(eq_reflexive(),[b]))
    pind_b=Phase3Ind(b,d,q1,sa,tape2,c1v)
    got_Pb=mp(got_Qb,got_orbb,or_bb,pind_b)
    got_Pb=eel(got_Pb,char_pv,pv);got_Pb=cut(got_Pb,Exists(pv,char_pv),got_ex_pv)
    print('phase3: P(b) extracted')

    # === Phase3Ind(b,...) → TMReaches(d,c1v,b,c2v) ===
    # Open Phase3Ind: ∃pos_b.And(Plus(sa,b,pos_b), ∃tra,cn.(...with TMConfig(cn,q1,pos_b,tape2)...))
    # TMConfig(c2v,q1,pos,tape2) with Plus(sa,b,pos): plus_val_unique → pos_b=pos → config_eq → cn=c2v
    # Then TMReaches from trace components.
    pb_exp=pind_b.expand();pb_pos=pb_exp.var;pb_body=pb_exp.body
    pb_plus=pb_body.left;pb_inner=pb_body.right
    pb_tra=pb_inner.var;pb_cn_ex=pb_inner.body;pb_cn=pb_cn_ex.var;pb_and=pb_cn_ex.body
    # Decompose pb_and
    b0=pb_and
    gft=apply_thm(and_elim_left(b0.left,b0.right,[]),[],b0,b0.left,ax(b0))
    b1=b0.right;gb1=apply_thm(and_elim_right(b0.left,b1,[]),[],b0,b1,ax(b0))
    b2=b1.right;gb2=apply_thm(and_elim_right(b1.left,b2,[]),[],b1,b2,gb1)
    gbt=apply_thm(and_elim_left(b2.left,b2.right,[]),[],b2,b2.left,gb2)
    b3=b2.right;gb3=apply_thm(and_elim_right(b2.left,b3,[]),[],b2,b3,gb2)
    gcnb=apply_thm(and_elim_left(b3.left,b3.right,[]),[],b3,b3.left,gb3)
    b4=b3.right;gb4=apply_thm(and_elim_right(b3.left,b4,[]),[],b3,b4,gb3)
    gatnb=apply_thm(and_elim_left(b4.left,b4.right,[]),[],b4,b4.left,gb4)
    gsvb=apply_thm(and_elim_right(b4.left,b4.right,[]),[],b4,b4.right,gb4)
    got_plus_b=apply_thm(and_elim_left(pb_plus,pb_inner,[]),[],pb_body,pb_plus,ax(pb_body))
    # Plus(sa,b,pos_b) and Plus(sa,b,pos): plus_val_unique → pos_b=pos
    from theorems.arithmetic import plus_val_unique
    _pvu=plus_val_unique()
    got_eq_pos=apply_thm(_pvu,[w,sa,b,pb_pos,pos])
    got_eq_pos=mp(got_eq_pos,ax(omega_w),omega_w,got_eq_pos.sequent.right[0].right)
    got_eq_pos=mp(got_eq_pos,ax(in_sa_w),in_sa_w,got_eq_pos.sequent.right[0].right)
    got_eq_pos=mp(got_eq_pos,ax(in_b_w),in_b_w,got_eq_pos.sequent.right[0].right)
    got_eq_pos=mp(got_eq_pos,got_plus_b,pb_plus,got_eq_pos.sequent.right[0].right)
    got_eq_pos=mp(got_eq_pos,ax(plus_sab),plus_sab,Eq(pb_pos,pos))
    # TMConfig(cn,q1,pos_b,tape2) + TMConfig(c2v,q1,pos,tape2) + Eq(pos_b,pos) → Eq(cn,c2v)
    # config_eq_transfer + ordpair_unique: TMConfig(cn,...pos_b...) → transfer pos_b→pos via Eq → same as c2v
    # Actually: Eq(pos_b,pos) → TMConfig(cn,q1,pos,tape2) via config_eq_transfer.
    # Then TMConfig(cn,q1,pos,tape2) + TMConfig(c2v,q1,pos,tape2) → Eq(cn,c2v) via config_eq/ordpair.
    from theorems.tm import config_eq_transfer
    _cet=config_eq_transfer()
    got_cfg_cn_pos=apply_thm(_cet,[pb_cn,q1,pb_pos,tape2,q1,pos,tape2])
    got_cfg_cn_pos=mp(got_cfg_cn_pos,gcnb,gcnb.sequent.right[0],got_cfg_cn_pos.sequent.right[0].right)
    got_cfg_cn_pos=mp(got_cfg_cn_pos,apply_thm(eq_reflexive(),[q1]),Eq(q1,q1),got_cfg_cn_pos.sequent.right[0].right)
    got_cfg_cn_pos=mp(got_cfg_cn_pos,got_eq_pos,Eq(pb_pos,pos),got_cfg_cn_pos.sequent.right[0].right)
    got_cfg_cn_pos=mp(got_cfg_cn_pos,apply_thm(eq_reflexive(),[tape2]),Eq(tape2,tape2),got_cfg_cn_pos.sequent.right[0].right)
    # TMConfig(pb_cn,q1,pos,tape2). config_eq → Eq(pb_cn,c2v) via ordpair_unique
    inner_v=Var(postfix='_iv');op_iv=OrdPair(inner_v,pos,tape2)
    got_ex_iv=apply_thm(_oe_fn(),[pos,tape2],concl=Exists(inner_v,op_iv))
    op_cn=OrdPair(pb_cn,q1,inner_v);op_c2=OrdPair(c2v,q1,inner_v)
    got_op_cn=apply_thm(got_cfg_cn_pos,[inner_v],op_iv,op_cn,ax(op_iv))
    got_op_c2=apply_thm(ax(cfg_c2),[inner_v],op_iv,op_c2,ax(op_iv))
    _ou=_ou_fn()
    got_eq_cn_c2=apply_thm(_ou,[q1,inner_v,pb_cn,c2v])
    got_eq_cn_c2=mp(got_eq_cn_c2,got_op_cn,op_cn,got_eq_cn_c2.sequent.right[0].right)
    got_eq_cn_c2=mp(got_eq_cn_c2,got_op_c2,op_c2,Eq(pb_cn,c2v))
    got_eq_cn_c2=eel(got_eq_cn_c2,op_iv,inner_v);got_eq_cn_c2=cut(got_eq_cn_c2,Exists(inner_v,op_iv),got_ex_iv)
    # Apply(tra,b,c2v) from Apply(tra,b,cn)+Eq(cn,c2v)
    _eavt=eq_apply_val_transfer()
    got_at_c2=apply_thm(_eavt,[pb_tra,b,pb_cn,c2v])
    got_at_c2=mp(got_at_c2,got_eq_cn_c2,Eq(pb_cn,c2v),got_at_c2.sequent.right[0].right)
    got_at_c2=mp(got_at_c2,gatnb,gatnb.sequent.right[0],Apply(pb_tra,b,c2v))
    # Build TMReaches
    reaches=TMReaches(d,c1v,b,c2v);rexp=reaches.expand();r_tra=rexp.var;r_body=rexp.body
    r_and=mk_and(gsvb,got_at_c2);r_and=mk_and(gbt,r_and)
    got_reaches=eir(r_and,r_body,r_tra,pb_tra)
    got_reaches=cut(ax(reaches),reaches,got_reaches)
    # eel eigenvars back into Phase3Ind
    got_reaches=eel(got_reaches,pb_and,pb_cn)
    got_reaches=eel(got_reaches,pb_cn_ex,pb_tra)
    # pn_body has pb_plus and pb_inner. inner was reformed via eel cn+tra above.
    # But pb_inner might still be separate on left. Cut it:
    got_inner_from_pb=apply_thm(and_elim_right(pb_plus,pb_inner,[]),[],pb_body,pb_inner,ax(pb_body))
    if any(same(pb_inner,f) for f in got_reaches.sequent.left):
        got_reaches=cut(got_reaches,pb_inner,got_inner_from_pb)
    got_reaches=eel(got_reaches,pb_body,pb_pos)
    got_reaches=cut(got_reaches,pind_b,got_Pb)
    print('phase3: TMReaches derived')

    # === Discharge + close → Phase3P ===
    goal_hyps=[trans,omega_w,in_b_w,in_sa_w,func_d,func_tape2,num_one,tape_read,plus_sab,cfg_c1,cfg_c2]
    for hyp in reversed(goal_hyps):
        got_reaches=wl(got_reaches,hyp);imp=Implies(hyp,got_reaches.sequent.right[0])
        left=[f for f in got_reaches.sequent.left if not same(f,hyp)]
        got_reaches=Proof(Sequent(left,[imp]),'implies_right',[got_reaches],principal=imp)
    for v in [c2v,c1v,one,w,tape2,pos,b,sa,q1,d]:
        body=got_reaches.sequent.right[0];fa=Forall(v,body)
        got_reaches=Proof(Sequent(got_reaches.sequent.left,[fa]),'forall_right',[got_reaches],principal=fa,term=v)
    goal=Phase3P()
    got_reaches=cut(ax(goal),goal,got_reaches)
    # Clean Num(z,0) leak
    from theorems.arithmetic import num_exists
    for f in list(got_reaches.sequent.left):
        if type(f).__name__=='Num' and f.value==0:
            got_reaches=eel(got_reaches,f,f.elem)
            got_reaches=cut(got_reaches,Exists(f.elem,f),num_exists(0))
            break
    assert same(got_reaches.sequent.right[0],goal,expand=False),'Phase3P mismatch'
    print('phase3: VERIFIED — proves Phase3P')
    got_reaches.name='phase3'
    return got_reaches


if __name__=='__main__':
    p=phase3()
    from core.zfc import ZFCAxiom
    non=[f for f in p.sequent.left if not isinstance(f,ZFCAxiom)]
    print(f'Left: {len(p.sequent.left)} total, {len(non)} non-ZFC')
    print(f'phase3_base: OK, non-ZFC={len(non)}')
