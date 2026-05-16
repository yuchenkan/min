"""Phase2P proof — single TM step: (q0,a,tape)→(q1,sa,tape2).

Transition: q0,zero→one,one(right),q1. Reads tape(a)=zero (separator),
writes one, moves right to sa=S(a), changes state to q1.

TMReaches for 1 step = TMStep wrapped via tmstep_to_reaches pattern.
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
from tm import UnaryTape
from tactics import apply_thm, mp, ax, fl, eir, eel, cut, wl, wr, weaken_to


def tape_read_sep():
    """|- ∀tape,a,b,zero. UnaryTape(tape,a,b) → Num(zero,0) → Apply(tape,a,zero)"""
    from theorems.logic import and_elim_left, and_elim_right

    tape, a, b, zero = Var(), Var(), Var(), Var()
    ut = UnaryTape(tape, a, b)
    num_zero = Num(zero, 0)
    app = Apply(tape, a, zero)

    exp = ut.expand()
    func_f = exp.left
    rest0 = exp.right
    low_f = rest0.left
    rest1 = rest0.right
    sep_f = rest1.left

    aer0 = and_elim_right(func_f, rest0, [])
    got_rest0 = apply_thm(aer0, [], ut, rest0, ax(ut))
    aer1 = and_elim_right(low_f, rest1, [])
    got_rest1 = apply_thm(aer1, [], rest0, rest1, got_rest0)
    ael1 = and_elim_left(sep_f, rest1.right, [])
    got_sep = apply_thm(ael1, [], rest1, sep_f, got_rest1)

    got = apply_thm(got_sep, [zero], num_zero, app, ax(num_zero))

    for premise in [num_zero, ut]:
        imp = Implies(premise, got.sequent.right[0])
        left = [f for f in got.sequent.left if not same(f, premise)]
        got = Proof(Sequent(left, [imp]), 'implies_right', [got], principal=imp)

    proof = got
    for v in [zero, b, a, tape]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]), 'forall_right',
            [proof], principal=fa, term=v)

    proof.name = 'tape_read_sep'
    return proof


def phase2():
    """ZFC |- Phase2P()
    Single TMStep: (q0,a,tape) → (q1,sa,tape2). Then tmstep_to_reaches."""
    from core.proof import Proof, Sequent, same, _subst
    from theorems.logic import (and_intro, and_elim_left, and_elim_right, eq_reflexive,
        eq_symmetric, eq_transitive)
    from theorems.sets import ordpair_exists, ordpair_eq_transfer
    from theorems.omega import func_unique_thm
    from theorems.tm import (Phase2P, config_decompose, apply_func_transfer,
        transition_unique, headmove_right_elim, config_eq_transfer,
        tape_update_eq_args)
    import core.zfc as zfc

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
    succ_sa=Successor(sa,a);tu_tape2=TapeUpdate(tape2,tape,a,one)
    cfg_c1=TMConfig(c1,q0,a,tape);cfg_c2=TMConfig(c2,q1,sa,tape2)

    # === Build TMStep(d,c1,c2) ===
    # TMStep = ∀q,h,t,sym,w,dir,qn,hn,tn.
    #   Config(c1,q,h,t)→Apply(t,h,sym)→Trans(d,q,sym,w,dir,qn)→
    #   TapeUpdate(tn,t,h,w)→HeadMove(h,hn,dir)→Config(c2,qn,hn,tn)
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

    # Step 2: Apply(tape,a,sym) → sym=zero via func_unique + tape_read_sep
    # Transfer Apply(t,h,sym) → Apply(tape,a,sym) via Eq(t,tape), Eq(h,a)
    aft=apply_func_transfer()
    from theorems.recursion import eq_apply_transfer
    eat=eq_apply_transfer()
    app_t_h_sym=Apply(tape,h,sym)
    got_app_th=apply_thm(aft,[t,tape,h,sym])
    got_app_th=mp(got_app_th,got_eq_t,eq_t,Implies(p_read,app_t_h_sym))
    got_app_th=mp(got_app_th,ax(p_read),p_read,app_t_h_sym)
    app_tape_a_sym=Apply(tape,a,sym)
    got_app_as=apply_thm(eat,[tape,h,a,sym])
    got_app_as=mp(got_app_as,got_eq_h,eq_h,Implies(app_t_h_sym,app_tape_a_sym))
    got_app_as=mp(got_app_as,got_app_th,app_t_h_sym,app_tape_a_sym)
    # tape_read_sep: Apply(tape,a,zero)
    _trs=tape_read_sep()
    got_app_az=apply_thm(_trs,[tape,a,Var(),zero])  # b is irrelevant, use fresh
    # Actually tape_read_sep: ∀tape,a,b,zero. UnaryTape→Num(zero,0)→Apply(tape,a,zero)
    # I don't have UnaryTape as hypothesis in Phase2P! But I do have Function(tape).
    # Hmm — Phase2P doesn't have UnaryTape. It has Function(tape) and tape_read_sep needs UnaryTape.
    # But Phase2P's hypotheses include: Function(tape), Num(zero,0), and the tape value at a
    # is implicitly zero because of how tm_add_correct chains things.
    # Wait — Phase2P doesn't directly give tape(a)=zero. It gives TMTransition(d,q0,zero,...).
    # The tape read value (sym) must match the transition's read symbol (zero).
    # Actually for TMStep: Apply(tape,h,sym) and TMTransition(d,q,sym,...). The sym in both
    # is the SAME variable. So I don't need to separately prove tape(a)=zero.
    # The TMStep just requires that the sym from Apply matches the sym in TMTransition.
    # The transition_unique then gives the output components.
    #
    # So I don't need tape_read_sep at all for the TMStep body! The sym is universally
    # quantified inside TMStep — whatever tape reads at h, that's the sym used in the transition.
    # The transition_unique step will match: TMTransition(d,q,sym,...) vs TMTransition(d,q0,zero,...).
    # With Eq(q,q0) and the KNOWN transition, this gives Eq(sym,zero) + output components.
    #
    # Wait, transition_unique needs TWO transitions with same (d,q,sym):
    # p_trans = TMTransition(d,q,sym,...) and trans = TMTransition(d,q0,zero,one,one,q1).
    # With Eq(q,q0): both have state q0. But sym vs zero: need Eq(sym,zero) first?
    # No — transition_unique compares outputs given SAME input. If input (q,sym)≠(q0,zero),
    # we can't compare. But Apply(tape,a,sym) means tape(a)=sym. And tape(a)=zero from
    # the tape structure. So sym=zero.
    #
    # Actually: Phase2P DOESN'T have UnaryTape as hypothesis. It only has Function(tape).
    # So there's no way to derive tape(a)=zero from Phase2P's hypotheses alone.
    # But we don't need to! The TMStep body has Apply(t,h,sym) as a hypothesis (inside the ∀).
    # We need to show: whatever sym is, the transition applies. But the transition is
    # TMTransition(d,q0,zero,...). It only fires on input (q0,zero). If sym≠zero, the
    # transition doesn't match and TMStep can't be proved.
    #
    # The trick: sym IS zero. Because Apply(t,h,sym)=Apply(tape,a,sym) (after transfers).
    # And Function(tape)→Apply(tape,a,sym)→Apply(tape,a,zero)→Eq(sym,zero) via func_unique
    # IF we can derive Apply(tape,a,zero). But how without UnaryTape?
    #
    # Hmm... looking at Phase2P's hypotheses again:
    # TMTransition(d,q0,zero,one,one,q1), Function(d), Function(tape),
    # Num(one,1), Num(zero,0), Successor(sa,a), TapeUpdate(tape2,tape,a,one),
    # TMConfig(c1,q0,a,tape), TMConfig(c2,q1,sa,tape2)
    #
    # There's no Apply(tape,a,zero) or UnaryTape! So how does the backup's phase2 work?
    # It uses tape_read_sep which needs UnaryTape. But backup's phase2 HAS UnaryTape.
    # The current Phase2P dropped UnaryTape from hypotheses.
    #
    # Wait, let me re-read Phase2P:
    # TMTransition(d,q0,zero,one,one,q1) → Function(d) → Function(tape) →
    # Num(one,1) → Num(zero,0) → Successor(sa,a) → TapeUpdate(tape2,tape,a,one) →
    # TMConfig(c1,q0,a,tape) → TMConfig(c2,q1,sa,tape2) → TMReaches(d,c1,one,c2)
    #
    # No Apply(tape,a,zero). No UnaryTape. So Phase2P's TMStep proof needs to work
    # WITHOUT knowing what tape(a) is. The TMStep body has Apply(t,h,sym) as hypothesis.
    # With Eq(q,q0)+Eq(h,a)+Eq(t,tape): this becomes Apply(tape,a,sym).
    # Function(d) + TMTransition(d,q0,zero,...) means delta is defined at (q0,zero).
    # But if sym≠zero, there's no transition at (q0,sym).
    # Actually: TMTransition just says Apply(delta,(q0,zero),(one,(one,q1))). It doesn't
    # say delta is UNDEFINED at other inputs. Function(delta) says it's single-valued.
    # So the TMStep body has TMTransition(d,q,sym,w,dir,qn) which is Apply(delta,(q,sym),(w,(dir,qn))).
    # And our known transition is Apply(delta,(q0,zero),(one,(one,q1))).
    # With Eq(q,q0): Apply(delta,(q0,sym),(w,(dir,qn))) and Apply(delta,(q0,zero),(one,(one,q1))).
    # If sym=zero: func_unique on delta → (w,(dir,qn))=(one,(one,q1)) → w=one,dir=one,qn=q1. ✓
    # If sym≠zero: we CAN'T derive anything from the known transition. TMStep fails.
    #
    # But TMStep is universally quantified: ∀q,h,t,sym,... TMConfig→Apply→Trans→TapeUpdate→HeadMove→Config.
    # We need to prove the CONCLUSION for ALL values of sym. But if sym≠zero, the
    # TMTransition(d,q,sym,...) on the LEFT gives us nothing useful.
    # UNLESS: we don't need to handle sym≠zero because Apply(tape,a,sym) and
    # TMTransition(d,q0,sym,w,d,qn) together with Function(d) force sym=zero.
    # Because: Apply(tape,a,sym) means ⟨(q0,sym),(w,(dir,qn))⟩ ∈ delta (from TMTransition).
    # And from our known transition: ⟨(q0,zero),(one,(one,q1))⟩ ∈ delta.
    # Function(delta): same input → same output. Input is (q0,sym) vs (q0,zero).
    # If sym≠zero, these are DIFFERENT inputs. Function(d) doesn't help.
    # So TMTransition(d,q,sym,...) with sym≠zero gives a DIFFERENT pair in delta.
    #
    # The resolution: the TMStep construction doesn't need sym=zero explicitly.
    # It uses: TMTransition(d,q,sym,w,dir,qn) [from TMStep ∀ hypothesis] and
    # TMTransition(d,q0,zero,one,one,q1) [from Phase2P hypothesis].
    # With Eq(q,q0): both are TMTransition(d,q0,sym,...) and TMTransition(d,q0,zero,...).
    # transition_unique gives: if same (d,q,sym), then same output.
    # But sym vs zero: they're the same only if sym=zero.
    # transition_unique actually gives: Function(d)→Trans(d,q,sym,w1,d1,qn1)→Trans(d,q,sym,w2,d2,qn2)→Eq(w1,w2)∧...
    # Both transitions have the SAME q,sym as second/third arg? No:
    # p_trans = TMTransition(d,q,sym,w_v,dir_v,qn) — reads (q,sym)
    # trans = TMTransition(d,q0,zero,one,one,q1) — reads (q0,zero)
    # These have SAME (q,sym) only if q=q0 AND sym=zero.
    # We have Eq(q,q0). But we DON'T have Eq(sym,zero) yet.
    #
    # So we need Eq(sym,zero). This comes from func_unique on TAPE:
    # Function(tape) + Apply(tape,a,sym) + Apply(tape,a,zero) → Eq(sym,zero).
    # But Apply(tape,a,zero) requires tape(a)=zero, which we can't derive without UnaryTape.
    #
    # CONCLUSION: Phase2P as defined is UNPROVABLE without knowing tape(a)=zero.
    # The definition needs either UnaryTape or Apply(tape,a,zero) as a hypothesis.
    #
    # But wait — looking at how Phase2P is used in tm_add_correct:
    # tm_add_correct provides UnaryTape(tape_in,a,b) → tape_read_sep → Apply(tape_in,a,zero).
    # Then Phase2P is applied with these. But Phase2P's ∀ quantification over tape means
    # Phase2P must work for ANY tape function, not just UnaryTape ones.
    #
    # Hmm, but Phase2P doesn't quantify over b (the second group size). Let me re-check...
    # Actually Phase2P DOES work: the key is TapeUpdate(tape2,tape,a,one). This MODIFIES
    # position a from whatever it was to one. The TMStep reads whatever tape(a) is (sym),
    # writes w=one regardless, and changes state. We don't need sym=zero for the WRITE part.
    # We need it for the TRANSITION MATCH: the known transition fires on input (q0,zero).
    # If tape(a)≠zero, this transition doesn't fire and we can't prove TMStep.
    #
    # So Phase2P IS unprovable as stated? Or am I missing something about how TMStep works?
    #
    # Let me re-read TMStep definition carefully:
    # TMStep(d,c1,c2) = ∀q,h,t,sym,w,d_,qn,hn,tn.
    #   Config(c1,q,h,t) → Apply(t,h,sym) → Trans(d,q,sym,w,d_,qn) →
    #   TapeUpdate(tn,t,h,w) → HeadMove(h,hn,d_) → Config(c2,qn,hn,tn)
    #
    # This says: for ANY decomposition of c1 into (q,h,t), if tape reads sym at h,
    # and transition maps (q,sym)→(w,d_,qn), and tape update and head move are consistent,
    # THEN c2 is the resulting config.
    #
    # The key: this must hold for ALL q,h,t,sym etc. But c1 = (q0,a,tape) has a UNIQUE
    # decomposition. So q=q0, h=a, t=tape (from config_decompose). Then sym is whatever
    # tape(a) is. And Trans(d,q0,sym,...) only exists if delta is defined at (q0,sym).
    # If delta ISN'T defined at (q0,sym), then Trans(d,q0,sym,...) is false (no pair in delta).
    # In that case, the implication is VACUOUSLY TRUE (false hypothesis).
    #
    # So: if sym≠zero and delta isn't defined at (q0,sym), TMStep is vacuously true!
    # And if sym=zero, we use the known transition.
    #
    # But Function(d) means delta IS defined everywhere? No! Function just means single-valued
    # (at most one output per input). It doesn't mean total.
    #
    # So TMStep IS provable: for sym where no transition exists, it's vacuous.
    # For the specific decomposition q=q0, h=a, t=tape:
    # - If Trans(d,q0,sym,w,d_,qn) holds AND Trans(d,q0,zero,one,one,q1) holds:
    #   func_unique on delta → same output → sym=zero (from pair injection on input).
    #   Wait no: both transitions have DIFFERENT read symbols if sym≠zero.
    #   Trans(d,q0,sym,...) means ⟨(q0,sym),out1⟩ ∈ delta.
    #   Trans(d,q0,zero,...) means ⟨(q0,zero),out2⟩ ∈ delta.
    #   Function(delta): same INPUT → same output. (q0,sym) and (q0,zero) are SAME input
    #   only if sym=zero. Otherwise different inputs.
    #
    # Actually transition_unique in the backup works by:
    # Given TWO Trans with same (d,q,sym), derive output equality.
    # In TMStep body: Trans(d,q,sym,w,d_,qn) is on the LEFT. Our known transition has
    # different sym (zero vs arbitrary sym). We can't directly apply transition_unique.
    #
    # The RIGHT approach for TMStep proof:
    # Trans(d,q,sym,w,d_,qn) on LEFT means Apply(delta,(q,sym),(w,(d_,qn))).
    # Known: Apply(delta,(q0,zero),(one,(one,q1))).
    # With Eq(q,q0): Apply(delta,(q0,sym),(w,(d_,qn))) and Apply(delta,(q0,zero),(one,(one,q1))).
    # These share delta as the function. func_unique on delta:
    # If same input: (q0,sym)=(q0,zero) → sym=zero, and output (w,(d_,qn))=(one,(one,q1)).
    # But func_unique gives: same FIRST arg of Apply → same output.
    # Apply(delta, INPUT1, OUTPUT1) and Apply(delta, INPUT2, OUTPUT2) with INPUT1=INPUT2 → OUTPUT1=OUTPUT2.
    # INPUT1=(q,sym) as ordpair. INPUT2=(q0,zero) as ordpair.
    # With Eq(q,q0): INPUT1=(q0,sym), INPUT2=(q0,zero). These are equal iff sym=zero.
    # If sym≠zero, they're different inputs and func_unique doesn't apply.
    #
    # So the TMStep body proof goes:
    # From Trans(d,q,sym,...) we get Apply(delta,inp1,out1) where inp1=(q,sym).
    # From known trans we get Apply(delta,inp2,out2) where inp2=(q0,zero).
    # Transfer inp1 using Eq(q,q0): inp1 becomes (q0,sym). Call it inp1'.
    # func_unique on delta: Apply(delta,inp1',out1) and Apply(delta,inp2,out2).
    # If inp1'=inp2 (i.e. (q0,sym)=(q0,zero) i.e. sym=zero): out1=out2. ✓
    # If inp1'≠inp2: we can't derive anything. But we don't need to!
    # In the TMStep body, Trans(d,q,sym,w,d_,qn) is a HYPOTHESIS (on the left).
    # If it's false (no such transition exists), the whole implication is vacuously true.
    # So we need to handle: ASSUMING Trans(d,q,sym,...) holds, derive Config(c2,...).
    # If Trans holds with sym≠zero: delta maps (q0,sym) to (w,(d_,qn)). And delta maps
    # (q0,zero) to (one,(one,q1)). These are consistent (different inputs, possibly
    # different outputs). We can't derive what w,d_,qn are from the known transition.
    # But we need to prove Config(c2,qn,hn,tn). Without knowing qn,hn,tn, we can't.
    #
    # ... Unless the TMStep proof uses a DIFFERENT strategy: directly show that c2's
    # config structure matches the transition output. The backup does this via
    # transition_unique on inputs with SAME (d,q,sym). Since both Trans hypotheses
    # in the TMStep body and the known transition have the same delta and the same
    # input pair (after transfer), func_unique DOES apply.
    #
    # Wait: the known transition has input (q0,zero). The TMStep's Trans has input (q,sym).
    # After Eq(q,q0), it's (q0,sym). For func_unique to apply, we need inp=(q0,sym)=(q0,zero),
    # i.e. sym=zero. But sym is universally quantified in TMStep.
    #
    # I think the key insight I'm missing: in the TMStep proof, we DON'T separately prove
    # Eq(sym,zero). Instead, we build the ordpair for (q,sym) from the TMStep's Trans,
    # and the ordpair for (q0,zero) from the known trans. Then func_unique on delta
    # with these two Apply's gives Eq(out1,out2) — which requires SAME INPUT.
    # The kernel checks: Apply(delta,inp1,out1) ∧ Apply(delta,inp2,out2) ∧ Function(delta).
    # func_unique gives Eq(out1,out2) IF inp1=inp2.
    # But we also derive Eq(inp1,inp2) from the func_unique on delta? No.
    #
    # Actually func_unique is: Function(f)→Apply(f,x,y1)→Apply(f,x,y2)→Eq(y1,y2).
    # It requires the SAME x (first arg). So I need Apply(delta,INP,out1) and Apply(delta,INP,out2)
    # with the SAME INP.
    #
    # In phase1_step_tmstep, the approach is:
    # 1. Build ordpair inp=(q,sym) from TMStep's Trans.
    # 2. Build ordpair inp2=(q0,one) from known trans.
    # 3. Transfer inp=(q,sym) to inp'=(q0,sym) via Eq(q,q0).
    #    Then to inp''=(q0,one) via Eq(sym,one) [which was derived from func_unique on tape].
    # 4. Now inp''=inp2. func_unique on delta with same input gives Eq(out1,out2).
    #
    # So phase1_step_tmstep DOES derive Eq(sym,one) first (via func_unique on tape)
    # and THEN uses it to transfer the input pair. I was wrong — it does need tape(a)=one
    # (or tape(a)=zero for phase2).
    #
    # For Phase2P: I need Apply(tape,a,zero) to derive Eq(sym,zero).
    # But Phase2P doesn't have UnaryTape or Apply(tape,a,zero) as hypothesis.
    #
    # CONCLUSION: Phase2P needs Apply(tape,a,zero) added, OR it's proved differently.
    # Let me check how tm_add_correct uses Phase2P — maybe it provides tape_read_sep's result.
    print('Phase2P analysis: needs Apply(tape,a,zero) — checking tm_add_correct usage')


if __name__ == '__main__':
    phase2()
