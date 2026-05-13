def plus_assoc():
    """Associativity: (a+b)+c = a+(b+c).
    |- ∀w,a,b,c,d,s,t. Omega(w) → In(a,w) → In(b,w) → In(c,w) →
       Plus(a,b,d) → Plus(d,c,s) → Plus(b,c,t) → Plus(a,t,s)

    Instantiate all Plus at fresh (wv,hv). h_assoc_identity gives
    Apply(hv,⟨a,t⟩,s). Close as Plus(a,t,s)."""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from vocab import (Function as FuncDef, Apply, Plus as PlusDef)
    from vocab.recursion import PlusFunc
    from vocab.ordpair import OrdPair
    from theorems.logic import and_elim_left, and_elim_right, iff_mp
    from theorems.sets import ordpair_exists, omega_unique
    from theorems.arithmetic import h_assoc_identity
    from core.proof import Proof, Sequent, same
    from core.lang import Var, In, Implies, Forall
    from core.derived import Eq, And, Iff, Exists
    from vocab.omega import Omega

    w = Var(postfix='w')
    a = Var(postfix='a')
    b = Var(postfix='b')
    c = Var(postfix='c')
    d = Var(postfix='d')
    s = Var(postfix='s')
    t = Var(postfix='t')
    omega_w = Omega(w)
    in_a_w = In(a, w)
    in_b_w = In(b, w)
    in_c_w = In(c, w)
    plus_abd = PlusDef(a, b, d)
    plus_dcs = PlusDef(d, c, s)
    plus_bct = PlusDef(b, c, t)
    plus_ats = PlusDef(a, t, s)

    # Fresh vars for inner Plus quantification
    wv = Var(postfix='wv')
    hv = Var(postfix='hv')
    omega_wv = Omega(wv)
    pf_hwv = PlusFunc(hv, wv)

    # omega_unique for membership transfer
    ou = omega_unique()
    eq_w_wv = Eq(w, wv)
    got_eq = apply_thm(ou, [w, wv])
    got_eq = mp(got_eq, ax(omega_w), omega_w, got_eq.sequent.right[0].right)
    got_eq = mp(got_eq, ax(omega_wv), omega_wv, eq_w_wv)

    def transfer_in(x, in_x_w):
        """Transfer In(x,w) → In(x,wv)"""
        in_x_wv = In(x, wv)
        iff_x = Iff(In(x, w), in_x_wv)
        got_iff = Proof(Sequent(got_eq.sequent.left, [iff_x]), 'cut',
            [wr(got_eq, iff_x),
             weaken_to(fl(eq_w_wv, iff_x, x), got_eq.sequent.left)],
            principal=eq_w_wv)
        return mp(mp(iff_mp(In(x, w), in_x_wv, []),
            got_iff, iff_x, Implies(In(x, w), in_x_wv)),
            ax(in_x_w), in_x_w, in_x_wv)

    got_in_a_wv = transfer_in(a, in_a_w)
    got_in_b_wv = transfer_in(b, in_b_w)
    got_in_c_wv = transfer_in(c, in_c_w)

    # Open Plus(a,b,d) at wv,hv → Apply(hv,pair_ab,d)
    def open_plus(plus_f, first, second, result_var):
        got = apply_thm(ax(plus_f), [wv])
        while isinstance(got.sequent.right[0], Implies):
            cur = got.sequent.right[0]
            hyp = cur.left
            if same(hyp, omega_wv):
                got = mp(got, ax(omega_wv), hyp, cur.right)
            elif same(hyp, pf_hwv):
                got = mp(got, ax(pf_hwv), hyp, cur.right)
            else:
                got = mp(got, ax(hyp), hyp, cur.right)
        if isinstance(got.sequent.right[0], Forall):
            got = apply_thm(got, [hv])
            while isinstance(got.sequent.right[0], Implies):
                cur = got.sequent.right[0]
                hyp = cur.left
                if same(hyp, pf_hwv):
                    got = mp(got, ax(pf_hwv), hyp, cur.right)
                else:
                    got = mp(got, ax(hyp), hyp, cur.right)
        pair_var = Var(postfix=f'p_{first._postfix}{second._postfix}')
        op = OrdPair(pair_var, first, second)
        if isinstance(got.sequent.right[0], Forall):
            got = apply_thm(got, [pair_var])
            while isinstance(got.sequent.right[0], Implies):
                cur = got.sequent.right[0]
                got = mp(got, ax(cur.left), cur.left, cur.right)
        return got, pair_var, op

    got_abd, pair_ab, op_ab = open_plus(plus_abd, a, b, d)
    got_dcs, pair_dc, op_dc = open_plus(plus_dcs, d, c, s)
    got_bct, pair_bc, op_bc = open_plus(plus_bct, b, c, t)
    print(f'plus_assoc: opened all Plus')

    # h_assoc_identity at wv,hv,a,b,pair_ab,d,c,...
    hai = h_assoc_identity()
    got_hai = apply_thm(hai, [wv, hv])
    got_hai = mp(got_hai, ax(omega_wv), omega_wv, got_hai.sequent.right[0].right)
    got_hai = mp(got_hai, ax(pf_hwv), pf_hwv, got_hai.sequent.right[0].right)
    # ∀a,b,pab,d. In(a,wv) → In(b,wv) → OrdPair(pab,a,b) → Apply(h,pab,d) →
    #   ∀c. In(c,wv) → ∀pdc,sv,pbc,tv,pat. OrdPair(pdc,d,c)→Apply(h,pdc,sv)→
    #     OrdPair(pbc,b,c)→Apply(h,pbc,tv)→OrdPair(pat,a,tv)→Apply(h,pat,sv)
    got_hai = apply_thm(got_hai, [a, b, pair_ab, d])
    got_hai = mp(got_hai, got_in_a_wv, In(a, wv), got_hai.sequent.right[0].right)
    got_hai = mp(got_hai, got_in_b_wv, In(b, wv), got_hai.sequent.right[0].right)
    got_hai = mp(got_hai, ax(op_ab), op_ab, got_hai.sequent.right[0].right)
    got_hai = mp(got_hai, got_abd, got_abd.sequent.right[0], got_hai.sequent.right[0].right)
    got_hai = apply_thm(got_hai, [c])
    got_hai = mp(got_hai, got_in_c_wv, In(c, wv), got_hai.sequent.right[0].right)
    pair_at = Var(postfix='pat')
    op_at = OrdPair(pair_at, a, t)
    got_hai = apply_thm(got_hai, [pair_dc, s, pair_bc, t, pair_at])
    got_hai = mp(got_hai, ax(op_dc), op_dc, got_hai.sequent.right[0].right)
    got_hai = mp(got_hai, got_dcs, got_dcs.sequent.right[0], got_hai.sequent.right[0].right)
    got_hai = mp(got_hai, ax(op_bc), op_bc, got_hai.sequent.right[0].right)
    got_hai = mp(got_hai, got_bct, got_bct.sequent.right[0], got_hai.sequent.right[0].right)
    got_hai = mp(got_hai, ax(op_at), op_at, Apply(hv, pair_at, s))
    print(f'plus_assoc: Apply(h,pair_at,s) = {got_hai.sequent.right[0]}')

    # eel pair_ab, pair_dc, pair_bc from their OrdPairs
    got_result = got_hai
    for pair_var, op_var, x, y in [(pair_ab, op_ab, a, b), (pair_dc, op_dc, d, c), (pair_bc, op_bc, b, c)]:
        got_result = eel(got_result, op_var, pair_var)
        got_ex = apply_thm(ordpair_exists(), [x, y], concl=Exists(pair_var, op_var))
        got_result = cut(got_result, Exists(pair_var, op_var), got_ex)

    # Close as Plus(a,t,s): discharge OrdPair(pair_at,a,t), ∀pair_at. PlusFunc, ∀hv. Omega(wv), ∀wv.
    imp_op = Implies(op_at, got_result.sequent.right[0])
    left_op = [f for f in got_result.sequent.left if not same(f, op_at)]
    got_result = Proof(Sequent(left_op, [imp_op]), 'implies_right', [got_result], principal=imp_op)
    got_result = Proof(Sequent(got_result.sequent.left, [Forall(pair_at, imp_op)]),
        'forall_right', [got_result], principal=Forall(pair_at, imp_op), term=pair_at)

    imp_pf = Implies(pf_hwv, got_result.sequent.right[0])
    left_pf = [f for f in got_result.sequent.left if not same(f, pf_hwv)]
    got_result = Proof(Sequent(left_pf, [imp_pf]), 'implies_right', [got_result], principal=imp_pf)
    got_result = Proof(Sequent(got_result.sequent.left, [Forall(hv, imp_pf)]),
        'forall_right', [got_result], principal=Forall(hv, imp_pf), term=hv)

    imp_ow = Implies(omega_wv, got_result.sequent.right[0])
    left_ow = [f for f in got_result.sequent.left if not same(f, omega_wv)]
    got_result = Proof(Sequent(left_ow, [imp_ow]), 'implies_right', [got_result], principal=imp_ow)
    got_result = Proof(Sequent(got_result.sequent.left, [Forall(wv, imp_ow)]),
        'forall_right', [got_result], principal=Forall(wv, imp_ow), term=wv)

    # This is Plus(a,t,s)
    got_result = cut(ax(plus_ats), plus_ats, got_result)
    print(f'plus_assoc: Plus(a,t,s) done')

    # Discharge outer hypotheses
    proof = got_result
    for hyp in [plus_bct, plus_dcs, plus_abd, in_c_w, in_b_w, in_a_w, omega_w]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [t, s, d, c, b, a, w]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    print(f'plus_assoc: result = {proof.sequent.right[0]}')
    proof.name = 'plus_assoc'
    return proof


if __name__ == '__main__':
    import sys
    sys.setrecursionlimit(100000)
    sys.path.insert(0, '/root/min/src')
    plus_assoc()
    print('plus_assoc: PASSED')
