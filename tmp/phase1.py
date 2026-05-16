"""Phase1P proof — proper vocab, pure sub-theorems."""
import sys; sys.path.insert(0, '/root/min/src')
from core.lang import Var, In, Not, Implies, Forall
from core.derived import Exists, And, Or, Iff, Eq
from core.proof import Proof, Sequent, same
from vocab.ordpair import OrdPair, Successor
from vocab.omega import Omega, Num
from vocab.sets import Empty, Singleton, TransitiveSet
from vocab.tm import TMConfig, TMTransition, TMStep, TMReaches
from vocab.functions import Function as FuncDef, Apply
from tm import UnaryTape
from tactics import apply_thm, mp, ax, fl, eir, eel, cut, wl, wr, weaken_to
from theorems.logic import (and_intro, and_elim_left, and_elim_right,
    or_intro_left, or_intro_right, or_elim,
    eq_reflexive, eq_symmetric, iff_mp, iff_mp_rev, unique_empty, eq_substitution)
from theorems.sets import (eq_transfer, ordpair_exists,
    omega_transitive_set as ots_fn, singleton_exists)
from theorems.omega import omega_contains_empty, omega_succ_closed
from theorems.tm import tape_read_low, phase1_step_tmstep, phase1_step_extend_trace
from theorems.recursion import singleton_is_function, singleton_apply_eq, eq_apply_transfer
import core.zfc as zfc


class Phase1Ind:
    """Strong induction predicate for Phase1 trace construction.
    Phase1Ind(n, d, q0, tape, c0) =
      ∃trace,cn. Function(trace) ∧ dom_bound(trace,n) ∧ base_cond(trace,c0) ∧
                 TMConfig(cn,q0,n,tape) ∧ Apply(trace,n,cn) ∧ step_valid(trace,n,d)"""
    __match_args__ = ('n', 'd', 'q0', 'tape', 'c0')
    def __init__(self, n, d, q0, tape, c0):
        self.n = n; self.d = d; self.q0 = q0; self.tape = tape; self.c0 = c0
    def expand(self):
        tra = Var(postfix='_tra'); cn = Var(postfix='_cn')
        k = Var(postfix='_k'); sk = Var(postfix='_sk')
        ck = Var(postfix='_ck'); ck1 = Var(postfix='_ck1')
        zp = Var(postfix='_zp')
        xd = Var(postfix='_xd'); yd = Var(postfix='_yd')
        base_cond = Forall(zp, Implies(Empty(zp), Apply(tra, zp, self.c0)))
        dom_bound = Forall(xd, Forall(yd, Implies(Apply(tra, xd, yd),
            Or(In(xd, self.n), Eq(xd, self.n)))))
        step_valid = Forall(k, Implies(In(k, self.n),
            Forall(sk, Implies(Successor(sk, k),
                Forall(ck, Implies(Apply(tra, k, ck),
                    Exists(ck1, And(Apply(tra, sk, ck1), TMStep(self.d, ck, ck1)))))))))
        return Exists(tra, Exists(cn, And(FuncDef(tra),
            And(dom_bound,
            And(base_cond,
            And(TMConfig(cn, self.q0, self.n, self.tape),
            And(Apply(tra, self.n, cn),
                step_valid)))))))
    def subst(self, old, new):
        r = lambda f: new if f is old else f
        return Phase1Ind(r(self.n), r(self.d), r(self.q0), r(self.tape), r(self.c0))
    def __str__(self):
        return f'P1Ind({self.n},{self.d},{self.q0},{self.tape},{self.c0})'



def phase1_base():
    """Pairing |- ∀d,q0,z,tape,c0. Num(z,0) → TMConfig(c0,q0,z,tape) → Phase1Ind(z,d,q0,tape,c0)"""
    def mk_and(gl, gr):
        L, R = gl.sequent.right[0], gr.sequent.right[0]
        return mp(apply_thm(and_intro(L, R, []), [], L, Implies(R, And(L, R)), gl), gr, R, And(L, R))

    d=Var(postfix='d');q0=Var(postfix='q0');z=Var(postfix='z')
    tape=Var(postfix='tape');c0=Var(postfix='c0')
    num_z=Num(z,0);cfg_c0=TMConfig(c0,q0,z,tape)
    goal = Phase1Ind(z, d, q0, tape, c0)

    # Build singleton trace {z→c0}
    pair_zc0=Var(postfix='pzc');t_sing=Var(postfix='ts')
    op_pair=OrdPair(pair_zc0,z,c0);sing_t=Singleton(t_sing,pair_zc0)
    oe=ordpair_exists();got_ex_pair=apply_thm(oe,[z,c0],concl=Exists(pair_zc0,op_pair))
    sif=singleton_is_function()
    got_func_s=apply_thm(sif,[pair_zc0,z,c0,t_sing])
    got_func_s=mp(got_func_s,ax(op_pair),op_pair,got_func_s.sequent.right[0].right)
    got_func_s=mp(got_func_s,ax(sing_t),sing_t,FuncDef(t_sing))

    # Apply(t_sing,z,c0)
    iff_is=Iff(In(pair_zc0,t_sing),Eq(pair_zc0,pair_zc0))
    got_iff_s=apply_thm(ax(sing_t),[pair_zc0],concl=iff_is)
    got_epp=apply_thm(eq_reflexive(),[pair_zc0])
    got_inp=mp(apply_thm(iff_mp_rev(In(pair_zc0,t_sing),Eq(pair_zc0,pair_zc0),[]),[],
        iff_is,Implies(Eq(pair_zc0,pair_zc0),In(pair_zc0,t_sing)),got_iff_s),
        got_epp,Eq(pair_zc0,pair_zc0),In(pair_zc0,t_sing))
    got_app_s=eir(mk_and(ax(op_pair),got_inp),And(op_pair,In(pair_zc0,t_sing)),pair_zc0,pair_zc0)

    # base_cond: ∀zp. Empty(zp) → Apply(t_sing,zp,c0)
    zp=Var(postfix='_zp')
    ue=unique_empty();es=eq_symmetric();eat=eq_apply_transfer()
    got_ezz=apply_thm(ue,[zp],Empty(zp),Forall(z,Implies(num_z,Eq(zp,z))),ax(Empty(zp)))
    got_ezz=apply_thm(got_ezz,[z],num_z,Eq(zp,z),ax(num_z))
    got_ezzp=apply_thm(es,[zp,z],Eq(zp,z),Eq(z,zp),got_ezz)
    got_azp=apply_thm(eat,[t_sing,z,zp,c0])
    got_azp=mp(got_azp,got_ezzp,Eq(z,zp),Implies(Apply(t_sing,z,c0),Apply(t_sing,zp,c0)))
    got_azp=mp(got_azp,got_app_s,Apply(t_sing,z,c0),Apply(t_sing,zp,c0))
    imp_b=Implies(Empty(zp),Apply(t_sing,zp,c0))
    lb=[f for f in got_azp.sequent.left if not same(f,Empty(zp))]
    got_bc=Proof(Sequent(lb,[imp_b]),'implies_right',[got_azp],principal=imp_b)
    got_bc=Proof(Sequent(got_bc.sequent.left,[Forall(zp,imp_b)]),'forall_right',[got_bc],principal=Forall(zp,imp_b),term=zp)

    # dom_bound: ∀xd,yd. Apply(t_sing,xd,yd) → Or(In(xd,z),Eq(xd,z))
    xd=Var(postfix='_xd');yd=Var(postfix='_yd')
    sae=singleton_apply_eq()
    got_sae=apply_thm(sae,[z,c0,pair_zc0,t_sing,xd,yd])
    got_sae=mp(got_sae,ax(op_pair),op_pair,got_sae.sequent.right[0].right)
    got_sae=mp(got_sae,ax(sing_t),sing_t,got_sae.sequent.right[0].right)
    got_sae=mp(got_sae,ax(Apply(t_sing,xd,yd)),Apply(t_sing,xd,yd),got_sae.sequent.right[0].right)
    got_ezxd=apply_thm(and_elim_left(Eq(z,xd),Eq(c0,yd),[]),[],got_sae.sequent.right[0],Eq(z,xd),got_sae)
    got_exdz=apply_thm(es,[z,xd],Eq(z,xd),Eq(xd,z),got_ezxd)
    or_xdz=Or(In(xd,z),Eq(xd,z))
    got_orx=apply_thm(or_intro_right(In(xd,z),Eq(xd,z),[]),[],Eq(xd,z),or_xdz,got_exdz)
    imp_db=Implies(Apply(t_sing,xd,yd),or_xdz)
    ldb=[f for f in got_orx.sequent.left if not same(f,Apply(t_sing,xd,yd))]
    got_db=Proof(Sequent(ldb,[imp_db]),'implies_right',[got_orx],principal=imp_db)
    got_db=Proof(Sequent(got_db.sequent.left,[Forall(yd,imp_db)]),'forall_right',[got_db],principal=Forall(yd,imp_db),term=yd)
    got_db=Proof(Sequent(got_db.sequent.left,[Forall(xd,Forall(yd,imp_db))]),'forall_right',[got_db],principal=Forall(xd,Forall(yd,imp_db)),term=xd)

    # step_valid: vacuous (∀k∈z=∅, impossible)
    _k=Var(postfix='_k');_sk=Var(postfix='_sk');_ck=Var(postfix='_ck');_ck1=Var(postfix='_ck1')
    got_nkz=apply_thm(ax(num_z),[_k])
    sv_inner=Forall(_sk,Implies(Successor(_sk,_k),Forall(_ck,Implies(Apply(t_sing,_k,_ck),Exists(_ck1,And(Apply(t_sing,_sk,_ck1),TMStep(d,_ck,_ck1)))))))
    nkz=Not(In(_k,z));gb=Proof(Sequent([In(_k,z),nkz],[]),'not_left',[ax(In(_k,z))],principal=nkz)
    gb=Proof(Sequent(gb.sequent.left,[sv_inner]),'weakening_right',[gb],principal=sv_inner)
    gb=cut(gb,nkz,got_nkz)
    imp_sv=Implies(In(_k,z),sv_inner);lsv=[f for f in gb.sequent.left if not same(f,In(_k,z))]
    got_sv=Proof(Sequent(lsv,[imp_sv]),'implies_right',[gb],principal=imp_sv)
    got_sv=Proof(Sequent(got_sv.sequent.left,[Forall(_k,imp_sv)]),'forall_right',[got_sv],principal=Forall(_k,imp_sv),term=_k)

    # Assemble Phase1Ind(z,...) via And + eir
    pza=mk_and(got_app_s,got_sv);pza=mk_and(ax(cfg_c0),pza)
    pza=mk_and(got_bc,pza);pza=mk_and(got_db,pza);pza=mk_and(got_func_s,pza)
    # eir: use goal.expand() structure
    exp = goal.expand()  # Exists(tra, Exists(cn, And(...)))
    tra_v = exp.var; inner_ex = exp.body  # Exists(cn, And(...))
    cn_v = inner_ex.var; and_body = inner_ex.body  # And(Function(tra), And(db, ...))
    # pza has the And with t_sing and c0. eir cn_v=c0, tra_v=t_sing.
    # Body for cn eir: and_body with tra_v=t_sing (cn_v free)
    from core.proof import _subst
    body_cn = _subst(and_body, tra_v, t_sing)  # And with t_sing, cn_v still free
    got_ecn = eir(pza, body_cn, cn_v, c0)
    # Body for trace eir: inner_ex with tra_v free
    got_etr = eir(got_ecn, inner_ex, tra_v, t_sing)
    assert same(got_etr.sequent.right[0], goal), f'Phase1Ind(z) mismatch'

    # eel singleton eigenvars
    se2=singleton_exists();got_es=apply_thm(se2,[pair_zc0],concl=Exists(t_sing,sing_t))
    got_etr=eel(got_etr,sing_t,t_sing);got_etr=cut(got_etr,Exists(t_sing,sing_t),got_es)
    got_etr=eel(got_etr,op_pair,pair_zc0);got_etr=cut(got_etr,Exists(pair_zc0,op_pair),got_ex_pair)

    # Discharge + ∀-close
    for hyp in [cfg_c0, num_z]:
        got_etr=wl(got_etr,hyp);imp=Implies(hyp,got_etr.sequent.right[0])
        left=[f for f in got_etr.sequent.left if not same(f,hyp)]
        got_etr=Proof(Sequent(left,[imp]),'implies_right',[got_etr],principal=imp)
    for v in [c0,tape,z,q0,d]:
        body=got_etr.sequent.right[0];fa=Forall(v,body)
        got_etr=Proof(Sequent(got_etr.sequent.left,[fa]),'forall_right',[got_etr],principal=fa,term=v)
    got_etr.name='phase1_base'
    return got_etr


def phase1_step_case():
    """ZFC |- ∀d,q0,a,b,tape,c0,n,sn,w,one.
        TMTransition(d,q0,one,one,one,q0) → Omega(w) → In(a,w) → In(n,w) →
        Function(d) → Function(tape) → Num(one,1) → UnaryTape(tape,a,b) →
        Successor(sn,n) → In(n,a) → Phase1Ind(n,d,q0,tape,c0) → Phase1Ind(sn,d,q0,tape,c0)"""
    def mk_and(gl, gr):
        L, R = gl.sequent.right[0], gr.sequent.right[0]
        return mp(apply_thm(and_intro(L, R, []), [], L, Implies(R, And(L, R)), gl), gr, R, And(L, R))

    d=Var(postfix='d');q0=Var(postfix='q0');a=Var(postfix='a');b=Var(postfix='b')
    tape=Var(postfix='tape');c0=Var(postfix='c0')
    n=Var(postfix='n');sn=Var(postfix='sn');w=Var(postfix='w');one=Var(postfix='one')
    trans=TMTransition(d,q0,one,one,one,q0);omega_w=Omega(w);in_a_w=In(a,w)
    func_d=FuncDef(d);func_tape=FuncDef(tape);num_one=Num(one,1)
    utape=UnaryTape(tape,a,b);succ_sn=Successor(sn,n)
    pn=Phase1Ind(n,d,q0,tape,c0);psn=Phase1Ind(sn,d,q0,tape,c0)

    # Decompose Phase1Ind(n,...) by expanding
    pn_exp = pn.expand()  # Exists(tra, Exists(cn, And(...)))
    tra_v = pn_exp.var; pn_inner = pn_exp.body
    cn_v = pn_inner.var; pn_and = pn_inner.body
    # pn_and = And(Func(tra), And(db(tra,n), And(bc(tra), And(TMConfig(cn,q0,n,tape), And(Apply(tra,n,cn), sv(tra,n))))))
    b0=pn_and
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

    # tape_read_low: In(n,a) → Apply(tape,n,one)
    _trl=tape_read_low()
    gat=apply_thm(_trl,[tape,a,b,n,one])
    gat=mp(gat,ax(utape),utape,gat.sequent.right[0].right)
    gat=mp(gat,ax(In(n,a)),In(n,a),gat.sequent.right[0].right)
    gat=mp(gat,ax(num_one),num_one,Apply(tape,n,one))

    # phase1_step_tmstep: ∃cn_new. And(TMConfig(cn_new,q0,sn,tape), TMStep(d,cn,cn_new))
    _pst=phase1_step_tmstep()
    gts=apply_thm(_pst,[d,q0,n,sn,tape,cn_v,one,one])
    gts=mp(gts,ax(func_d),func_d,gts.sequent.right[0].right)
    gts=mp(gts,ax(trans),trans,gts.sequent.right[0].right)
    gts=mp(gts,gcn,gcn.sequent.right[0],gts.sequent.right[0].right)
    gts=mp(gts,ax(func_tape),func_tape,gts.sequent.right[0].right)
    gts=mp(gts,gat,Apply(tape,n,one),gts.sequent.right[0].right)
    gts=mp(gts,ax(num_one),num_one,gts.sequent.right[0].right)
    gts=mp(gts,ax(succ_sn),succ_sn,gts.sequent.right[0].right)

    # Open ∃cn_new
    tsx=gts.sequent.right[0];cnw=tsx.var;tsb=tsx.body
    gcfn=apply_thm(and_elim_left(tsb.left,tsb.right,[]),[],tsb,tsb.left,ax(tsb))
    gstn=apply_thm(and_elim_right(tsb.left,tsb.right,[]),[],tsb,tsb.right,ax(tsb))

    # phase1_step_extend_trace
    _pet=phase1_step_extend_trace()
    gext=apply_thm(_pet,[tra_v,sn,cnw,c0,n,d,cn_v,w])
    gext=mp(gext,gft,gft.sequent.right[0],gext.sequent.right[0].right)
    gext=mp(gext,gdb,gdb.sequent.right[0],gext.sequent.right[0].right)
    gext=mp(gext,ax(omega_w),omega_w,gext.sequent.right[0].right)
    gext=mp(gext,ax(In(n,w)),In(n,w),gext.sequent.right[0].right)
    gext=mp(gext,ax(succ_sn),succ_sn,gext.sequent.right[0].right)
    gext=mp(gext,gbt,gbt.sequent.right[0],gext.sequent.right[0].right)
    gext=mp(gext,gsvn,gsvn.sequent.right[0],gext.sequent.right[0].right)
    gext=mp(gext,gstn,gstn.sequent.right[0],gext.sequent.right[0].right)
    gext=mp(gext,gatn,gatn.sequent.right[0],gext.sequent.right[0].right)

    # Open ∃trn, decompose, insert TMConfig, reassemble Phase1Ind(sn,...)
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

    # Reassemble with TMConfig(cnw,q0,sn,tape) inserted
    psna=mk_and(geap,gesv);psna=mk_and(gcfn,psna);psna=mk_and(gebc,psna)
    psna=mk_and(gedb,psna);psna=mk_and(gef,psna)

    # eir using psn.expand() structure
    psn_exp=psn.expand();psn_tra=psn_exp.var;psn_inner=psn_exp.body
    psn_cn=psn_inner.var;psn_and=psn_inner.body
    from core.proof import _subst
    body_cn2=_subst(psn_and,psn_tra,trn)
    got_ecn2=eir(psna,body_cn2,psn_cn,cnw)
    got_etr2=eir(got_ecn2,psn_inner,psn_tra,trn)
    assert same(got_etr2.sequent.right[0],psn),f'Phase1Ind(sn) mismatch'

    # eel eigenvars
    got_etr2=eel(got_etr2,extb,trn);got_etr2=cut(got_etr2,extx,gext)
    got_etr2=eel(got_etr2,tsb,cnw);got_etr2=cut(got_etr2,tsx,gts)
    got_etr2=eel(got_etr2,pn_and,cn_v);got_etr2=cut(got_etr2,pn_inner,ax(pn_inner))
    got_etr2=eel(got_etr2,pn_inner,tra_v);got_etr2=cut(got_etr2,pn_exp,ax(pn))

    # Discharge + ∀-close
    hyps=[pn,In(n,a),succ_sn,num_one,utape,func_tape,func_d,In(n,w),in_a_w,omega_w,trans]
    for hyp in hyps:
        got_etr2=wl(got_etr2,hyp);imp=Implies(hyp,got_etr2.sequent.right[0])
        left=[f for f in got_etr2.sequent.left if not same(f,hyp)]
        got_etr2=Proof(Sequent(left,[imp]),'implies_right',[got_etr2],principal=imp)
    for v in [one,w,sn,n,c0,tape,b,a,q0,d]:
        body=got_etr2.sequent.right[0];fa=Forall(v,body)
        got_etr2=Proof(Sequent(got_etr2.sequent.left,[fa]),'forall_right',[got_etr2],principal=fa,term=v)
    got_etr2.name='phase1_step_case'
    return got_etr2


def phase1():
    """ZFC |- Phase1P()
    Omega induction using phase1_base + phase1_step_case, then extract TMReaches."""
    from core.proof import _var_free_in_sequent
    from theorems.omega import omega_smallest_inductive
    from theorems.tm import Phase1P

    def mk_and(gl, gr):
        L, R = gl.sequent.right[0], gr.sequent.right[0]
        return mp(apply_thm(and_intro(L, R, []), [], L, Implies(R, And(L, R)), gl), gr, R, And(L, R))

    d=Var(postfix='d');q0=Var(postfix='q0');z=Var(postfix='z')
    a=Var(postfix='a');tape=Var(postfix='tape');c0=Var(postfix='c0');c1=Var(postfix='c1')
    w=Var(postfix='w');one=Var(postfix='one');b=Var(postfix='b')
    n=Var(postfix='ind_n');sn=Var(postfix='ind_sn')
    pv=Var(postfix='ind_pv');xv=Var(postfix='ind_xv')
    trans=TMTransition(d,q0,one,one,one,q0);omega_w=Omega(w);in_a_w=In(a,w)
    func_d=FuncDef(d);func_tape=FuncDef(tape);num_one=Num(one,1);num_z=Num(z,0)
    utape=UnaryTape(tape,a,b);cfg_c0=TMConfig(c0,q0,z,tape);cfg_c1=TMConfig(c1,q0,a,tape)
    succ_sn=Successor(sn,n)
    pind_n = Phase1Ind(n,d,q0,tape,c0)

    def Q(nn): return Implies(Or(In(nn,a),Eq(nn,a)), Phase1Ind(nn,d,q0,tape,c0))

    # Separation
    # Q has free vars: a, d, q0, tape, c0 (plus nn which is the separation var)
    # Phase1Ind(nn,...).expand() introduces bound vars internally
    sep=zfc.Separation(Q,[a,d,q0,tape,c0])
    sep_ax=Proof(Sequent([sep],[sep]),'axiom',principal=sep)
    char_pv=Forall(xv,Iff(In(xv,pv),And(In(xv,w),Q(xv))))
    got_ex_pv=apply_thm(sep_ax,[c0,tape,q0,d,a,w],concl=Exists(pv,char_pv))

    def char_bwd(term,got_in_w,got_Q):
        gi=apply_thm(ax(char_pv),[term]);ii=gi.sequent.right[0];af=ii.right
        gr=apply_thm(iff_mp_rev(ii.left,ii.right,[]),[],ii,Implies(af,ii.left),gi)
        ai2=and_intro(af.left,af.right,[])
        ga=apply_thm(ai2,[],af.left,Implies(af.right,af),got_in_w)
        gand=mp(ga,got_Q,af.right,af);return mp(gr,gand,af,ii.left)

    def char_fwd(term):
        gi=apply_thm(ax(char_pv),[term]);ii=gi.sequent.right[0]
        gimp=apply_thm(iff_mp(ii.left,ii.right,[]),[],ii,Implies(ii.left,ii.right),gi)
        return mp(gimp,ax(In(term,pv)),In(term,pv),ii.right)

    print('phase1: sep done')

    # === BASE: In(z,pv) ===
    oce=omega_contains_empty()
    got_z_w=apply_thm(oce,[w],omega_w,Forall(z,Implies(num_z,In(z,w))),ax(omega_w))
    got_z_w=apply_thm(got_z_w,[z],num_z,In(z,w),ax(num_z))

    _pb=phase1_base()
    # _pb: Pairing |- ∀d,q0,z,tape,c0. Num(z,0)→TMConfig(c0,q0,z,tape)→Phase1Ind(z,d,q0,tape,c0)
    got_pb=apply_thm(_pb,[d,q0,z,tape,c0])
    got_pb=mp(got_pb,ax(num_z),num_z,got_pb.sequent.right[0].right)
    got_pb=mp(got_pb,ax(cfg_c0),cfg_c0,got_pb.sequent.right[0].right)
    # |- Phase1Ind(z,d,q0,tape,c0)

    # Q(z) = Or(In(z,a),Eq(z,a)) → Phase1Ind(z,...). Weaken with Or.
    or_za=Or(In(z,a),Eq(z,a))
    got_Qz=wl(got_pb,or_za)
    imp_qz=Implies(or_za,got_Qz.sequent.right[0])
    lqz=[f for f in got_Qz.sequent.left if not same(f,or_za)]
    got_Qz=Proof(Sequent(lqz,[imp_qz]),'implies_right',[got_Qz],principal=imp_qz)

    got_base_pv=char_bwd(z,got_z_w,got_Qz)

    # Inductive base: ∀zero_v. Empty(zero_v) → In(zero_v,pv)
    zero_v=Var(postfix='ind_zero')
    ue=unique_empty();es_thm=eq_substitution()
    got_eq=apply_thm(ue,[zero_v],Empty(zero_v),Forall(z,Implies(num_z,Eq(zero_v,z))),ax(Empty(zero_v)))
    got_eq=apply_thm(got_eq,[z],num_z,Eq(zero_v,z),ax(num_z))
    iff_zv=Iff(In(zero_v,pv),In(z,pv))
    got_iff=apply_thm(es_thm,[zero_v,z,pv],Eq(zero_v,z),iff_zv,got_eq)
    got_zv_pv=mp(apply_thm(iff_mp_rev(In(zero_v,pv),In(z,pv),[]),[],iff_zv,Implies(In(z,pv),In(zero_v,pv)),got_iff),
        got_base_pv,In(z,pv),In(zero_v,pv))
    imp_ez=Implies(Empty(zero_v),In(zero_v,pv))
    lez=[f for f in got_zv_pv.sequent.left if not same(f,Empty(zero_v))]
    got_ind_base=Proof(Sequent(lez,[imp_ez]),'implies_right',[got_zv_pv],principal=imp_ez)
    got_ind_base=Proof(Sequent(got_ind_base.sequent.left,[Forall(zero_v,imp_ez)]),
        'forall_right',[got_ind_base],principal=Forall(zero_v,imp_ez),term=zero_v)
    print('phase1: ind_base done')

    # === STEP: In(n,pv) → In(sn,pv) ===
    got_an=char_fwd(n)
    got_in_nw=apply_thm(and_elim_left(In(n,w),Q(n),[]),[],got_an.sequent.right[0],In(n,w),got_an)
    got_Qn=apply_thm(and_elim_right(In(n,w),Q(n),[]),[],got_an.sequent.right[0],Q(n),got_an)

    osc=omega_succ_closed()
    got_snw=apply_thm(osc,[w],omega_w,Forall(n,Implies(In(n,w),Forall(sn,Implies(succ_sn,In(sn,w))))),ax(omega_w))
    got_snw=apply_thm(got_snw,[n],In(n,w),Forall(sn,Implies(succ_sn,In(sn,w))),got_in_nw)
    got_snw=apply_thm(got_snw,[sn],succ_sn,In(sn,w),ax(succ_sn))

    # In(n,a) from Or(In(sn,a),Eq(sn,a)) via TransitiveSet(a)
    or_sna=Or(In(sn,a),Eq(sn,a))
    or_nsn=Or(In(n,n),Eq(n,n));iff_nsn=Iff(In(n,sn),or_nsn)
    got_insn=apply_thm(ax(succ_sn),[n],concl=iff_nsn)
    got_orn=apply_thm(or_intro_right(In(n,n),Eq(n,n),[]),[],Eq(n,n),or_nsn,apply_thm(eq_reflexive(),[n]))
    got_insn=mp(apply_thm(iff_mp_rev(In(n,sn),or_nsn,[]),[],iff_nsn,Implies(or_nsn,In(n,sn)),got_insn),got_orn,or_nsn,In(n,sn))
    _ots=ots_fn();gta=apply_thm(_ots,[w,a]);gta=mp(gta,ax(omega_w),omega_w,gta.sequent.right[0].right)
    gta=mp(gta,ax(in_a_w),in_a_w,TransitiveSet(a))
    gc1=apply_thm(gta,[sn]);cur=gc1.sequent.right[0];gc1=mp(gc1,ax(In(sn,a)),cur.left,cur.right)
    gc1=apply_thm(gc1,[n]);cur=gc1.sequent.right[0];gc1=mp(gc1,got_insn,cur.left,cur.right)
    _et=eq_transfer();gis=apply_thm(_et,[sn,a,n]);gis=mp(gis,ax(Eq(sn,a)),Eq(sn,a),gis.sequent.right[0].right)
    gc2=mp(apply_thm(iff_mp(In(n,sn),In(n,a),[]),[],Iff(In(n,sn),In(n,a)),Implies(In(n,sn),In(n,a)),gis),got_insn,In(n,sn),In(n,a))
    ic1=Implies(In(sn,a),In(n,a));lc1=[f for f in gc1.sequent.left if not same(f,In(sn,a))]
    gic1=Proof(Sequent(lc1,[ic1]),'implies_right',[gc1],principal=ic1)
    ic2=Implies(Eq(sn,a),In(n,a));lc2=[f for f in gc2.sequent.left if not same(f,Eq(sn,a))]
    gic2=Proof(Sequent(lc2,[ic2]),'implies_right',[gc2],principal=ic2)
    oena=or_elim(In(sn,a),Eq(sn,a),In(n,a),[])
    got_ina=apply_thm(oena,[],or_sna,Implies(ic1,Implies(ic2,In(n,a))),ax(or_sna))
    got_ina=mp(got_ina,gic1,ic1,Implies(ic2,In(n,a)));got_ina=mp(got_ina,gic2,ic2,In(n,a))

    # Q(n) → Phase1Ind(n,...) via Or(In(n,a),Eq(n,a))
    or_na=Or(In(n,a),Eq(n,a))
    got_orna=apply_thm(or_intro_left(In(n,a),Eq(n,a),[]),[],In(n,a),or_na,got_ina)
    got_Pn=mp(got_Qn,got_orna,or_na,pind_n)

    # phase1_step_case → Phase1Ind(sn,...) via instantiation + mp
    _psc=phase1_step_case()
    got_psc=apply_thm(_psc,[d,q0,a,b,tape,c0,n,sn,w,one])
    # Print implication chain to determine correct mp order
    from core.lang import Implies as _Imp
    _r=got_psc.sequent.right[0]; _i=0
    while type(_r) is _Imp:
        print(f'  step_case imp {_i}: {str(_r.left)[:60]}')
        _r=_r.right; _i+=1
    print(f'  step_case concl: {str(_r)[:60]}')
    got_psc=mp(got_psc,ax(trans),trans,got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,ax(omega_w),omega_w,got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,ax(in_a_w),in_a_w,got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,got_in_nw,In(n,w),got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,ax(func_d),func_d,got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,ax(func_tape),func_tape,got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,ax(utape),utape,got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,ax(num_one),num_one,got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,ax(succ_sn),succ_sn,got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,got_ina,In(n,a),got_psc.sequent.right[0].right)
    got_psc=mp(got_psc,got_Pn,pind_n,got_psc.sequent.right[0].right)
    # |- Phase1Ind(sn,d,q0,tape,c0)

    # Q(sn) = Or(In(sn,a),Eq(sn,a)) → Phase1Ind(sn,...)
    pind_sn=Phase1Ind(sn,d,q0,tape,c0)
    imp_qsn=Implies(or_sna,pind_sn)
    lqsn=[f for f in got_psc.sequent.left if not same(f,or_sna)]
    got_Qsn=Proof(Sequent(lqsn,[imp_qsn]),'implies_right',[wl(got_psc,or_sna)],principal=imp_qsn)

    got_step_pv=char_bwd(sn,got_snw,got_Qsn)
    if any(same(In(n,w),f) for f in got_step_pv.sequent.left):
        got_step_pv=cut(got_step_pv,In(n,w),got_in_nw)
    print('phase1: step In(sn,pv) done')

    # Discharge sn, n
    proof=got_step_pv
    for ff in list(proof.sequent.left):
        if _var_free_in_sequent(sn,Sequent([ff],[])) and not same(ff,succ_sn):
            proof=wl(proof,ff);imp=Implies(ff,proof.sequent.right[0])
            left=[f for f in proof.sequent.left if not same(f,ff)]
            proof=Proof(Sequent(left,[imp]),'implies_right',[proof],principal=imp)
    imp_sn=Implies(succ_sn,proof.sequent.right[0])
    left_sn=[f for f in proof.sequent.left if not same(f,succ_sn)]
    proof=Proof(Sequent(left_sn,[imp_sn]),'implies_right',[proof],principal=imp_sn)
    proof=Proof(Sequent(proof.sequent.left,[Forall(sn,imp_sn)]),'forall_right',[proof],principal=Forall(sn,imp_sn),term=sn)
    for ff in list(proof.sequent.left):
        if _var_free_in_sequent(n,Sequent([ff],[])) and not same(ff,In(n,pv)):
            proof=wl(proof,ff);imp=Implies(ff,proof.sequent.right[0])
            left=[f for f in proof.sequent.left if not same(f,ff)]
            proof=Proof(Sequent(left,[imp]),'implies_right',[proof],principal=imp)
    imp_npv=Implies(In(n,pv),proof.sequent.right[0])
    left_npv=[f for f in proof.sequent.left if not same(f,In(n,pv))]
    got_ind_step=Proof(Sequent(left_npv,[imp_npv]),'implies_right',[proof],principal=imp_npv)
    got_ind_step=Proof(Sequent(got_ind_step.sequent.left,[Forall(n,imp_npv)]),'forall_right',[got_ind_step],principal=Forall(n,imp_npv),term=n)
    print('phase1: ind_step done')

    # === OSI ===
    all_ctx=list(got_ind_base.sequent.left)
    for f_ in got_ind_step.sequent.left:
        if not any(same(f_,g) for g in all_ctx): all_ctx.append(f_)
    gib_w=weaken_to(got_ind_base,all_ctx);gis_w=weaken_to(got_ind_step,all_ctx)
    ibf=gib_w.sequent.right[0];isf=gis_w.sequent.right[0];ai=And(ibf,isf)
    got_ind=mp(apply_thm(and_intro(ibf,isf,[]),[],ibf,Implies(isf,ai),gib_w),gis_w,isf,ai)

    xs2=Var(postfix='xs2');got_fwd=char_fwd(xs2)
    inxw=got_fwd.sequent.right[0].left
    got_xw=apply_thm(and_elim_left(inxw,got_fwd.sequent.right[0].right,[]),[],got_fwd.sequent.right[0],inxw,got_fwd)
    imp_sub=Implies(In(xs2,pv),inxw)
    ls=[f for f in got_xw.sequent.left if not same(f,In(xs2,pv))]
    got_sub=Proof(Sequent(ls,[imp_sub]),'implies_right',[got_xw],principal=imp_sub)
    spw=Forall(xs2,imp_sub)
    got_sub=Proof(Sequent(got_sub.sequent.left,[spw]),'forall_right',[got_sub],principal=spw,term=xs2)

    osi=omega_smallest_inductive();eq_pw=Eq(pv,w)
    got_osi=apply_thm(osi,[pv,w])
    while not same(got_osi.sequent.right[0],eq_pw):
        cur=got_osi.sequent.right[0];got_osi=mp(got_osi,ax(cur.left),cur.left,cur.right)
    all_osi=list(all_ctx)
    for f_ in got_sub.sequent.left:
        if not any(same(f_,g) for g in all_osi): all_osi.append(f_)
    gsw=weaken_to(got_sub,all_osi);giw=weaken_to(got_ind,all_osi)
    gas=mp(apply_thm(and_intro(spw,ai,[]),[],spw,Implies(ai,And(spw,ai)),gsw),giw,ai,And(spw,ai))
    for h in [f_ for f_ in got_osi.sequent.left if not isinstance(f_,zfc.ZFCAxiom) and not same(f_,omega_w)]:
        got_osi=cut(got_osi,h,gas)
    print('phase1: osi done')

    # === Extract Q(a) → Phase1Ind(a,...) ===
    iff_a=Iff(In(a,pv),In(a,w))
    got_iff_a=cut(fl(eq_pw,iff_a,a),eq_pw,got_osi)
    got_apv=mp(apply_thm(iff_mp_rev(In(a,pv),In(a,w),[]),[],iff_a,Implies(In(a,w),In(a,pv)),got_iff_a),ax(in_a_w),in_a_w,In(a,pv))
    got_anda=cut(char_fwd(a),In(a,pv),got_apv)
    got_Qa=apply_thm(and_elim_right(In(a,w),Q(a),[]),[],got_anda.sequent.right[0],Q(a),got_anda)
    or_aa=Or(In(a,a),Eq(a,a));got_oraa=apply_thm(or_intro_right(In(a,a),Eq(a,a),[]),[],Eq(a,a),or_aa,apply_thm(eq_reflexive(),[a]))
    pind_a=Phase1Ind(a,d,q0,tape,c0)
    got_Pa=mp(got_Qa,got_oraa,or_aa,pind_a)
    got_Pa=eel(got_Pa,char_pv,pv);got_Pa=cut(got_Pa,Exists(pv,char_pv),got_ex_pv)
    print('phase1: P(a) extracted')

    # === Phase1Ind(a,...) + TMConfig(c1,...) → TMReaches(d,c0,a,c1) ===
    # Put Phase1Ind(a,...) on left, open ∃tra,cn. Derive TMReaches(d,c0,a,c1).
    # cn is eigenvariable (not free on right since right has c1). tra also eigenvariable.
    pind_a=Phase1Ind(a,d,q0,tape,c0)
    pa_exp=pind_a.expand();pa_tra=pa_exp.var;pa_inner=pa_exp.body
    pa_cn=pa_inner.var;pa_and=pa_inner.body

    # Decompose pa_and from left
    b0=pa_and
    gft=apply_thm(and_elim_left(b0.left,b0.right,[]),[],b0,b0.left,ax(b0))
    b1=b0.right;gb1=apply_thm(and_elim_right(b0.left,b1,[]),[],b0,b1,ax(b0))
    b2=b1.right;gb2=apply_thm(and_elim_right(b1.left,b2,[]),[],b1,b2,gb1)
    gbt=apply_thm(and_elim_left(b2.left,b2.right,[]),[],b2,b2.left,gb2)
    b3=b2.right;gb3=apply_thm(and_elim_right(b2.left,b3,[]),[],b2,b3,gb2)
    gcna=apply_thm(and_elim_left(b3.left,b3.right,[]),[],b3,b3.left,gb3)
    b4=b3.right;gb4=apply_thm(and_elim_right(b3.left,b4,[]),[],b3,b4,gb3)
    gatna=apply_thm(and_elim_left(b4.left,b4.right,[]),[],b4,b4.left,gb4)
    gsva=apply_thm(and_elim_right(b4.left,b4.right,[]),[],b4,b4.right,gb4)
    # gcna: [pa_and] |- TMConfig(pa_cn,q0,a,tape)
    # gatna: [pa_and] |- Apply(pa_tra,a,pa_cn)
    # gbt: [pa_and] |- base_cond(pa_tra)
    # gsva: [pa_and] |- step_valid(pa_tra,a)

    # Eq(pa_cn,c1) from ordpair_unique on the config structure
    # TMConfig(cn,...) = ∀v. OrdPair(v,a,tape)→OrdPair(cn,q0,v)
    # TMConfig(c1,...) = ∀v. OrdPair(v,a,tape)→OrdPair(c1,q0,v)
    # Get a common inner pair via ordpair_exists, then ordpair_unique on outer.
    inner_v=Var(postfix='_iv');op_iv=OrdPair(inner_v,a,tape)
    got_ex_iv=apply_thm(ordpair_exists(),[a,tape],concl=Exists(inner_v,op_iv))
    # TMConfig(pa_cn,...) inst with inner_v: OrdPair(inner_v,a,tape)→OrdPair(pa_cn,q0,inner_v)
    op_cn=OrdPair(pa_cn,q0,inner_v)
    got_op_cn=apply_thm(gcna,[inner_v],op_iv,op_cn,ax(op_iv))
    # TMConfig(c1,...) inst with inner_v:
    op_c1=OrdPair(c1,q0,inner_v)
    got_op_c1=apply_thm(ax(cfg_c1),[inner_v],op_iv,op_c1,ax(op_iv))
    # ordpair_unique: OrdPair(pa_cn,q0,inner_v)→OrdPair(c1,q0,inner_v)→Eq(pa_cn,c1)
    from theorems.sets import ordpair_unique as _ou_fn
    _ou=_ou_fn()
    got_eq=apply_thm(_ou,[q0,inner_v,pa_cn,c1])
    got_eq=mp(got_eq,got_op_cn,op_cn,got_eq.sequent.right[0].right)
    got_eq=mp(got_eq,got_op_c1,op_c1,Eq(pa_cn,c1))
    # eel inner_v
    got_eq=eel(got_eq,op_iv,inner_v);got_eq=cut(got_eq,Exists(inner_v,op_iv),got_ex_iv)
    # [...] |- Eq(pa_cn,c1)

    # Apply(pa_tra,a,c1) from Apply(pa_tra,a,pa_cn) + Eq(pa_cn,c1)
    from theorems.recursion import eq_apply_val_transfer as _eavt_fn
    _eavt=_eavt_fn()
    got_at_c1=apply_thm(_eavt,[pa_tra,a,pa_cn,c1])
    got_at_c1=mp(got_at_c1,got_eq,Eq(pa_cn,c1),got_at_c1.sequent.right[0].right)
    got_at_c1=mp(got_at_c1,gatna,gatna.sequent.right[0],Apply(pa_tra,a,c1))

    # Build TMReaches(d,c0,a,c1) = ∃trace. And(base, And(step, Apply(trace,a,c1)))
    reaches=TMReaches(d,c0,a,c1)
    rexp=reaches.expand();r_tra=rexp.var;r_body=rexp.body
    r_and=mk_and(gsva,got_at_c1);r_and=mk_and(gbt,r_and)
    got_reaches=eir(r_and,r_body,r_tra,pa_tra)
    got_reaches=cut(ax(reaches),reaches,got_reaches)
    # [pa_and, TMConfig(c1,...), Pairing] |- TMReaches(d,c0,a,c1)
    # c1 is free on right. pa_cn is NOT free on right (only cn appears via pa_and on left).
    # pa_tra NOT free on right (eir bound it).
    # eel pa_cn from pa_and: pa_cn free in pa_and (left) but NOT on right. ✓
    got_reaches=eel(got_reaches,pa_and,pa_cn)
    # [Exists(pa_cn,pa_and)=pa_inner, TMConfig(c1,...), Pairing] |- TMReaches(d,c0,a,c1)
    # eel pa_tra from pa_inner: pa_tra free in pa_inner (left) but NOT on right. ✓
    got_reaches=eel(got_reaches,pa_inner,pa_tra)
    # [Exists(pa_tra,pa_inner)=pind_a, TMConfig(c1,...), Pairing] |- TMReaches(d,c0,a,c1)
    got_reaches=cut(got_reaches,pind_a,got_Pa)
    # [TMConfig(c1,...), Pairing, ...ZFC from got_Pa...] |- TMReaches(d,c0,a,c1)
    print(f'phase1: TMReaches(d,c0,a,c1) derived')

    # === Discharge + forall-close → Phase1P ===
    goal_hyps=[trans,omega_w,in_a_w,func_d,func_tape,num_one,num_z,utape,cfg_c0,cfg_c1]
    for hyp in reversed(goal_hyps):
        got_reaches=wl(got_reaches,hyp);imp=Implies(hyp,got_reaches.sequent.right[0])
        left=[f for f in got_reaches.sequent.left if not same(f,hyp)]
        got_reaches=Proof(Sequent(left,[imp]),'implies_right',[got_reaches],principal=imp)
    for v in [c1,c0,b,one,w,tape,a,z,q0,d]:
        body=got_reaches.sequent.right[0];fa=Forall(v,body)
        got_reaches=Proof(Sequent(got_reaches.sequent.left,[fa]),'forall_right',[got_reaches],principal=fa,term=v)

    # Wrap as Phase1P vocab object
    goal=Phase1P()
    got_reaches=cut(ax(goal),goal,got_reaches)
    assert same(got_reaches.sequent.right[0],goal,expand=False), \
        f'Phase1P mismatch'
    print('phase1: VERIFIED — proves Phase1P')
    got_reaches.name='phase1'
    return got_reaches


if __name__ == '__main__':
    p = phase1()
    print(f'\nLeft ({len(p.sequent.left)}):')
    for f in p.sequent.left:
        print(f'  {type(f).__name__}')
