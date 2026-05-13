def prove_addition(m_val, n_val):
    """Prove m + n = m+n for specific Python ints.
    |- ∀w,a,b,c. Omega(w) → Num(a,m_val) → Num(b,n_val) → Num(c,m_val+n_val) → Plus(a,b,c)"""
    from tactics import apply_thm, wl, wr, mp, ax, fl, eir, eel, cut, weaken_to
    from vocab import (Function as FuncDef, Apply, Plus as PlusDef,
        Successor as SuccDef, Num as NumDef)
    from vocab.recursion import PlusFunc
    from vocab.ordpair import OrdPair
    from vocab.sets import Empty
    from vocab.omega import Omega
    from theorems.logic import (and_intro, and_elim_left, and_elim_right,
        iff_mp, iff_mp_rev, eq_symmetric, unique_empty, eq_reflexive)
    from theorems.omega import (func_unique_thm, omega_contains_empty, omega_succ_closed)
    from theorems.sets import (ordpair_exists, successor_exists, unique_successor,
        eq_successor_transfer)
    from theorems.recursion import eq_apply_val_transfer
    from theorems.arithmetic import plusfunc_elim
    from core.proof import Proof, Sequent, same, _var_free_in_sequent
    from core.lang import Var, In, Implies, Forall
    from core.derived import Eq, And, Iff, Exists

    p_val = m_val + n_val
    w = Var(postfix='w')
    a = Var(postfix='a')
    b = Var(postfix='b')
    c = Var(postfix='c')
    omega_w = Omega(w)
    num_a = NumDef(a, m_val)
    num_b = NumDef(b, n_val)
    num_c = NumDef(c, p_val)
    plus_abc = PlusDef(a, b, c)

    wv = Var(postfix='wv')
    hv = Var(postfix='hv')
    omega_wv = Omega(wv)
    pf_hwv = PlusFunc(hv, wv)
    pair_ab = Var(postfix='pab')
    op_ab = OrdPair(pair_ab, a, b)

    got_func, got_dom, got_base_pf, got_step_pf, _ = plusfunc_elim(hv, wv)
    fu = func_unique_thm()
    es = eq_symmetric()
    eavt = eq_apply_val_transfer()
    oce = omega_contains_empty()
    osc = omega_succ_closed()
    oe = ordpair_exists()
    se = successor_exists()
    us = unique_successor()
    est = eq_successor_transfer()
    ue = unique_empty()
    er = eq_reflexive()

    from theorems.sets import omega_unique
    ou = omega_unique()
    eq_w_wv = Eq(w, wv)
    got_eq_wwv = apply_thm(ou, [w, wv])
    got_eq_wwv = mp(got_eq_wwv, ax(omega_w), omega_w, got_eq_wwv.sequent.right[0].right)
    got_eq_wwv = mp(got_eq_wwv, ax(omega_wv), omega_wv, eq_w_wv)
    def transfer_in(x, in_x_w):
        in_x_wv = In(x, wv)
        iff_x = Iff(In(x, w), in_x_wv)
        got_iff = Proof(Sequent(got_eq_wwv.sequent.left, [iff_x]), 'cut',
            [wr(got_eq_wwv, iff_x),
             weaken_to(fl(eq_w_wv, iff_x, x), got_eq_wwv.sequent.left)],
            principal=eq_w_wv)
        return mp(mp(iff_mp(In(x, w), in_x_wv, []),
            got_iff, iff_x, Implies(In(x, w), in_x_wv)),
            ax(in_x_w), in_x_w, in_x_wv)

    def mk_and(got_l, got_r):
        L, R_ = got_l.sequent.right[0], got_r.sequent.right[0]
        return mp(apply_thm(and_intro(L, R_, []), [], L, Implies(R_, And(L, R_)), got_l),
            got_r, R_, And(L, R_))

    # === Generate Num chains: lists of (var, empty/succ formula) ===
    # For Num(x, k): x_0 (empty), x_1=S(x_0), ..., x_{k-1}=S(x_{k-2}), x=S(x_{k-1})
    def make_num_chain(x, k, prefix):
        """Returns (vars, empty_var, succs) where vars=[x_0,...,x_{k-1}],
        empty_var has Empty(x_0), succs[i] = Succ(x_{i+1}, x_i) with succs[-1] = Succ(x, x_{k-1})."""
        if k == 0:
            return [], x, []  # x itself is empty
        vs = [Var(postfix=f'{prefix}{i}') for i in range(k)]
        empty_v = vs[0]
        succs = []
        for i in range(1, k):
            succs.append((vs[i], vs[i-1], SuccDef(vs[i], vs[i-1])))
        succs.append((x, vs[-1], SuccDef(x, vs[-1])))
        return vs, empty_v, succs

    a_vs, a_empty, a_succs = make_num_chain(a, m_val, 'a')
    b_vs, b_empty, b_succs = make_num_chain(b, n_val, 'b')
    c_vs, c_empty, c_succs = make_num_chain(c, p_val, 'c')

    # Empty formulas
    empty_a0 = Empty(a_empty)
    empty_b0 = Empty(b_empty)
    empty_c0 = Empty(c_empty)

    # === Derive In(a, wv) from omega membership chain ===
    def derive_in_wv(empty_var, succs, empty_f):
        """Derive In(x, wv) for x at the end of the chain."""
        got = apply_thm(oce, [wv])
        got = mp(got, ax(omega_wv), omega_wv, got.sequent.right[0].right)
        got = apply_thm(got, [empty_var])
        got = mp(got, ax(empty_f), empty_f, In(empty_var, wv))
        cur_var = empty_var
        results = {empty_var: got}
        for top, bot, succ_f in succs:
            got_next = apply_thm(osc, [wv])
            got_next = mp(got_next, ax(omega_wv), omega_wv, got_next.sequent.right[0].right)
            got_next = apply_thm(got_next, [bot])
            got_next = mp(got_next, results[bot], In(bot, wv), got_next.sequent.right[0].right)
            got_next = apply_thm(got_next, [top])
            got_next = mp(got_next, ax(succ_f), succ_f, In(top, wv))
            results[top] = got_next
        return results

    a_in_wv = derive_in_wv(a_empty, a_succs, empty_a0) if m_val > 0 else {}
    got_a_wv = a_in_wv[a] if m_val > 0 else (lambda: (
        apply_thm(oce, [wv]),
        mp(apply_thm(oce, [wv]), ax(omega_wv), omega_wv, apply_thm(oce, [wv]).sequent.right[0].right)
    ))  # handle m_val=0 case
    if m_val > 0:
        got_a_wv = a_in_wv[a]
    else:
        got_a_wv = apply_thm(oce, [wv])
        got_a_wv = mp(got_a_wv, ax(omega_wv), omega_wv, got_a_wv.sequent.right[0].right)
        got_a_wv = apply_thm(got_a_wv, [a])
        got_a_wv = mp(got_a_wv, ax(empty_a0), empty_a0, In(a, wv))

    b_in_wv = derive_in_wv(b_empty, b_succs, empty_b0) if n_val > 0 else {}

    # === PlusFunc computation: h(⟨a, b⟩) via base + n_val steps ===
    # h(⟨a, b_empty⟩) = a  (base, since b_empty is empty)
    # h(⟨a, b_succs[0].top⟩) = S(a)  (step 1)
    # ...
    # h(⟨a, b⟩) = S^{n_val}(a)

    if n_val == 0:
        # b itself is empty. h(⟨a,b⟩) = a. Need Eq(a,c) from Num(a,m_val), Num(c,m_val).
        # Actually p_val = m_val, so Num(c, m_val). a and c both represent m_val.
        # This case needs func_unique: Apply(h,pair_ab,c) from Apply(h,pair_ab,a) + Eq(a,c).
        # For now, skip — focus on n_val > 0.
        raise NotImplementedError("n_val=0 not implemented yet")

    # Base: h(⟨a, b_empty⟩) = a
    pair_base = Var(postfix='prB')
    op_a_b0 = OrdPair(pair_base, a, b_empty)
    got_h = apply_thm(got_base_pf, [a])
    got_h = mp(got_h, got_a_wv, In(a, wv), got_h.sequent.right[0].right)
    got_h = apply_thm(got_h, [b_empty])
    got_h = mp(got_h, ax(empty_b0), empty_b0, got_h.sequent.right[0].right)
    got_h = apply_thm(got_h, [pair_base])
    got_h = mp(got_h, ax(op_a_b0), op_a_b0, Apply(hv, pair_base, a))

    # Current value = a, current pair = pair_base, current b_var = b_empty
    cur_val = a
    cur_pair = pair_base
    cur_b = b_empty
    pairs_to_eel = [(pair_base, op_a_b0, a, b_empty)]
    succs_to_eel = []

    # Steps: for each succ in b_succs
    for i, (b_top, b_bot, succ_f) in enumerate(b_succs):
        new_val = Var(postfix=f'sv{i}')
        succ_new = SuccDef(new_val, cur_val)
        new_pair = Var(postfix=f'pr{i}')
        op_new = OrdPair(new_pair, a, b_top)

        got_in_bot = b_in_wv[b_bot] if b_bot in b_in_wv else got_a_wv  # shouldn't happen
        got_step = apply_thm(got_step_pf, [a])
        got_step = mp(got_step, got_a_wv, In(a, wv), got_step.sequent.right[0].right)
        got_step = apply_thm(got_step, [cur_b])
        got_step = mp(got_step, got_in_bot, In(cur_b, wv), got_step.sequent.right[0].right)
        got_step = apply_thm(got_step, [cur_pair])
        got_step = mp(got_step, ax(OrdPair(cur_pair, a, cur_b)), OrdPair(cur_pair, a, cur_b), got_step.sequent.right[0].right)
        got_step = apply_thm(got_step, [cur_val])
        got_step = mp(got_step, got_h, Apply(hv, cur_pair, cur_val), got_step.sequent.right[0].right)
        got_step = apply_thm(got_step, [b_top])
        got_step = mp(got_step, ax(succ_f), succ_f, got_step.sequent.right[0].right)
        got_step = apply_thm(got_step, [new_val])
        got_step = mp(got_step, ax(succ_new), succ_new, got_step.sequent.right[0].right)
        got_step = apply_thm(got_step, [new_pair])
        got_step = mp(got_step, ax(op_new), op_new, Apply(hv, new_pair, new_val))

        got_h = got_step
        pairs_to_eel.append((new_pair, op_new, a, b_top))
        succs_to_eel.append((new_val, succ_new, cur_val))
        cur_val = new_val
        cur_pair = new_pair
        cur_b = b_top

    print(f'prove_addition: h(⟨a,b⟩) = S^{n_val}(a) done, val={cur_val}')

    # === Show S^{n_val}(a) = c via Num chains ===
    # a = S^{m_val}(a_empty), c = S^{p_val}(c_empty).
    # S^{n_val}(a) = S^{n_val}(S^{m_val}(a_empty)) = S^{p_val}(a_empty).
    # c = S^{p_val}(c_empty). unique_empty: a_empty = c_empty.
    # Then chain eq_successor_transfer: S(a_empty) = S(c_empty) = c_vs[1], etc.

    # unique_empty: a_empty = c_empty
    got_eq_base = apply_thm(ue, [a_empty])
    got_eq_base = mp(got_eq_base, ax(empty_a0), empty_a0, got_eq_base.sequent.right[0].right)
    got_eq_base = apply_thm(got_eq_base, [c_empty])
    got_eq_base = mp(got_eq_base, ax(empty_c0), empty_c0, Eq(a_empty, c_empty))

    # Build equality chain: we need to show cur_val = c.
    # The value chain is: a_empty, a_vs[1], ..., a_vs[-1], a, sv0, sv1, ..., sv_{n-1} = cur_val
    # The c chain is: c_empty, c_vs[1], ..., c_vs[-1], c
    # Both have p_val = m_val + n_val elements.

    # Build the "value side" chain: a_empty, then a_succs, then the sv succs
    val_chain = [a_empty]  # val_chain[0]
    val_succs = []  # (top, bot, succ_formula)
    for top, bot, sf in a_succs:
        val_chain.append(top)
        val_succs.append((top, bot, sf))
    for new_val, succ_new, old_val in succs_to_eel:
        val_chain.append(new_val)
        val_succs.append((new_val, old_val, succ_new))

    # c chain: c_empty, then c_succs
    c_chain = [c_empty]
    c_succ_list = []
    for top, bot, sf in c_succs:
        c_chain.append(top)
        c_succ_list.append((top, bot, sf))

    assert len(val_chain) == len(c_chain) == p_val + 1, f'{len(val_chain)} vs {len(c_chain)} vs {p_val+1}'

    # Chain eq_successor_transfer: Eq(val_chain[i], c_chain[i]) for each i
    cur_eq = got_eq_base  # Eq(val_chain[0], c_chain[0]) = Eq(a_empty, c_empty)
    for i in range(p_val):
        v_top, v_bot, v_sf = val_succs[i]
        c_top, c_bot, c_sf = c_succ_list[i]
        # est: Eq(a,c) → Eq(b,d) → Succ(c,d) → Succ(a,b)
        # Want: Succ(c_top, c_bot) + Eq(v_bot, c_bot) → Succ(c_top, v_bot)
        # Then unique_successor: Succ(v_top, v_bot) + Succ(c_top, v_bot) → Eq(v_top, c_top)
        got_eq_cc = apply_thm(er, [c_top])
        got_succ_c_vbot = apply_thm(est, [c_top, v_bot, c_top, c_bot])
        got_succ_c_vbot = mp(got_succ_c_vbot, got_eq_cc, Eq(c_top, c_top), got_succ_c_vbot.sequent.right[0].right)
        got_succ_c_vbot = mp(got_succ_c_vbot, cur_eq, Eq(v_bot, c_bot), got_succ_c_vbot.sequent.right[0].right)
        got_succ_c_vbot = mp(got_succ_c_vbot, ax(c_sf), c_sf, SuccDef(c_top, v_bot))
        got_eq_next = apply_thm(us, [v_bot, v_top, c_top])
        got_eq_next = mp(got_eq_next, ax(v_sf), v_sf, got_eq_next.sequent.right[0].right)
        got_eq_next = mp(got_eq_next, got_succ_c_vbot, SuccDef(c_top, v_bot), Eq(v_top, c_top))
        cur_eq = got_eq_next

    # cur_eq: Eq(cur_val, c)
    print(f'prove_addition: Eq(cur_val, c) done')

    # Apply(h, cur_pair, cur_val) → Apply(h, cur_pair, c) via eavt
    got_result = apply_thm(eavt, [hv, cur_pair, cur_val, c])
    got_result = mp(got_result, cur_eq, Eq(cur_val, c), got_result.sequent.right[0].right)
    got_result = mp(got_result, got_h, Apply(hv, cur_pair, cur_val), Apply(hv, cur_pair, c))

    # Transfer to pair_ab: cur_pair is the last pair, which IS pair_ab (the last b_succ top is b)
    # Actually cur_pair = new_pair for the last step = pr{n_val-1}, and op_new = OrdPair(pr{n-1}, a, b).
    # We need Apply(h, pair_ab, c). cur_pair has OrdPair(cur_pair, a, b) on left.
    # ordpair_unique: pair_ab = cur_pair. Transfer.
    from theorems.sets import ordpair_unique
    ou2 = ordpair_unique()
    op_cur = OrdPair(cur_pair, a, b)
    eq_pab_cur = Eq(pair_ab, cur_pair)
    got_eq_pair = apply_thm(ou2, [a, b, pair_ab, cur_pair])
    got_eq_pair = mp(got_eq_pair, ax(op_ab), op_ab, got_eq_pair.sequent.right[0].right)
    got_eq_pair = mp(got_eq_pair, ax(op_cur), op_cur, eq_pab_cur)
    eq_cur_pab = Eq(cur_pair, pair_ab)
    got_eq_cur_pab = apply_thm(es, [pair_ab, cur_pair], eq_pab_cur, eq_cur_pab, got_eq_pair)
    from theorems.recursion import eq_apply_transfer
    eat = eq_apply_transfer()
    got_final = apply_thm(eat, [hv, cur_pair, pair_ab, c])
    got_final = mp(got_final, got_eq_cur_pab, eq_cur_pab, got_final.sequent.right[0].right)
    got_final = mp(got_final, got_result, Apply(hv, cur_pair, c), Apply(hv, pair_ab, c))
    print(f'prove_addition: Apply(h, pair_ab, c) done')

    # eel all intermediate pairs and successor vars
    # Reverse order: last created first
    for new_val, succ_new, old_val in reversed(succs_to_eel):
        got_final = eel(got_final, succ_new, new_val)
        got_ex = apply_thm(se, [old_val], concl=Exists(new_val, succ_new))
        got_final = cut(got_final, Exists(new_val, succ_new), got_ex)

    for pair_var, op_var, x, y in reversed(pairs_to_eel):
        got_final = eel(got_final, op_var, pair_var)
        got_ex = apply_thm(oe, [x, y], concl=Exists(pair_var, op_var))
        got_final = cut(got_final, Exists(pair_var, op_var), got_ex)

    # Close as Plus(a,b,c)
    imp_op = Implies(op_ab, got_final.sequent.right[0])
    left_op = [f for f in got_final.sequent.left if not same(f, op_ab)]
    got_final = Proof(Sequent(left_op, [imp_op]), 'implies_right', [got_final], principal=imp_op)
    got_final = Proof(Sequent(got_final.sequent.left, [Forall(pair_ab, imp_op)]),
        'forall_right', [got_final], principal=Forall(pair_ab, imp_op), term=pair_ab)
    imp_pf = Implies(pf_hwv, got_final.sequent.right[0])
    left_pf = [f for f in got_final.sequent.left if not same(f, pf_hwv)]
    got_final = Proof(Sequent(left_pf, [imp_pf]), 'implies_right', [got_final], principal=imp_pf)
    got_final = Proof(Sequent(got_final.sequent.left, [Forall(hv, imp_pf)]),
        'forall_right', [got_final], principal=Forall(hv, imp_pf), term=hv)
    imp_ow = Implies(omega_wv, got_final.sequent.right[0])
    left_ow = [f for f in got_final.sequent.left if not same(f, omega_wv)]
    got_final = Proof(Sequent(left_ow, [imp_ow]), 'implies_right', [got_final], principal=imp_ow)
    got_final = Proof(Sequent(got_final.sequent.left, [Forall(wv, imp_ow)]),
        'forall_right', [got_final], principal=Forall(wv, imp_ow), term=wv)
    got_final = cut(ax(plus_abc), plus_abc, got_final)
    print(f'prove_addition: Plus(a,b,c) done')

    # === Discharge Num hypotheses ===
    proof = got_final

    def discharge_num(proof, num_hyp, chain_empty, chain_succs, chain_vars):
        """Package individual Empty/Succ back into Num form and cut."""
        if len(chain_succs) == 0:
            # Num(x,0) = Empty(x). Already on left.
            return proof

        # Package from bottom up: And(Empty, Succ), eel, And with next Succ, eel, ...
        empty_f = Empty(chain_empty)
        # Level 0: And(Empty(v0), Succ(v1, v0))
        top0, bot0, sf0 = chain_succs[0]
        and_0 = And(empty_f, sf0)
        # Cut Empty from And
        got_el = apply_thm(and_elim_left(empty_f, sf0, []), [], and_0, empty_f, ax(and_0))
        proof = cut(proof, empty_f, got_el)
        got_er = apply_thm(and_elim_right(empty_f, sf0, []), [], and_0, sf0, ax(and_0))
        proof = cut(proof, sf0, got_er)
        proof = eel(proof, and_0, chain_empty)

        # Levels 1+: And(∃...prev..., Succ(v_{i+1}, v_i))
        cur_ex = Exists(chain_empty, and_0)  # = Num(top0, 1).expand()
        for i in range(1, len(chain_succs)):
            top_i, bot_i, sf_i = chain_succs[i]
            and_i = And(cur_ex, sf_i)
            got_el = apply_thm(and_elim_left(cur_ex, sf_i, []), [], and_i, cur_ex, ax(and_i))
            proof = cut(proof, cur_ex, got_el)
            got_er = apply_thm(and_elim_right(cur_ex, sf_i, []), [], and_i, sf_i, ax(and_i))
            proof = cut(proof, sf_i, got_er)
            proof = eel(proof, and_i, bot_i)
            cur_ex = Exists(bot_i, and_i)

        # cur_ex = Num(x, k).expand(). Cut with Num(x, k).
        proof = cut(proof, cur_ex, ax(num_hyp))
        return proof

    proof = discharge_num(proof, num_a, a_empty, a_succs, a_vs)
    print(f'prove_addition: Num(a,{m_val}) discharged')
    proof = discharge_num(proof, num_b, b_empty, b_succs, b_vs)
    print(f'prove_addition: Num(b,{n_val}) discharged')
    proof = discharge_num(proof, num_c, c_empty, c_succs, c_vs)
    print(f'prove_addition: Num(c,{p_val}) discharged')

    # Discharge Num hypotheses, then Omega
    for hyp in [num_c, num_b, num_a, omega_w]:
        if not any(same(hyp, f) for f in proof.sequent.left):
            proof = wl(proof, hyp)
        imp = Implies(hyp, proof.sequent.right[0])
        left = [f for f in proof.sequent.left if not same(f, hyp)]
        proof = Proof(Sequent(left, [imp]), 'implies_right', [proof], principal=imp)
    for v in [c, b, a, w]:
        body = proof.sequent.right[0]
        fa = Forall(v, body)
        proof = Proof(Sequent(proof.sequent.left, [fa]),
            'forall_right', [proof], principal=fa, term=v)

    print(f'prove_addition: result = {proof.sequent.right[0]}')
    proof.name = f'prove_addition_{m_val}_{n_val}'
    return proof


if __name__ == '__main__':
    import sys
    sys.setrecursionlimit(100000)
    sys.path.insert(0, '/root/min/src')
    prove_addition(2, 2)
    print('prove_addition(2,2): PASSED')
    prove_addition(2, 3)
    print('prove_addition(2,3): PASSED')
