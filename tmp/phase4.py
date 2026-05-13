def phase4():
    """Phase 4: single step (q1, S(c)) → (q2, c, tape2).
    Reads 0 at position S(c), writes 0, moves left to c.

    |- ∀delta,q0,q1,q2,tape_in,c0,z,a,b,c,w,one,d0,d1,sa,sc,zero_var.
         TMTransition(delta,q1,zero_var,zero_var,d0,q2) →
         Omega(w) → In(a,w) → In(b,w) → In(sa,w) → In(c,w) →
         Successor(sa,a) → Successor(sc,c) →
         Plus(a,b,c) → Plus(sa,b,sc) →
         UnaryTape(tape_in,a,b) → Function(delta) → Function(tape_in) →
         Num(one,1) → Num(d0,0) → Num(d1,1) → Num(zero_var,0) → Num(q2,3) →
         Phase3P(b,sa,q1,tape_in,c0,delta,a,one) →
         ... TODO
    """
    # Phase 4 takes P3(b) which gives us:
    # - TapeUpdate(tape2, tape_in, a, one)
    # - Plus(sa, b, pos) where pos is the head position = sc = S(c)
    # - TMConfig(cj, q1, pos, tape2)
    # - trace function with all prior steps
    #
    # Then:
    # 1. Read tape2 at pos: tape2(sc) = 0 (position after second group)
    # 2. TMTransition(delta, q1, zero_var, zero_var, d0, q2)
    # 3. TapeUpdate(tape2', tape2, sc, zero_var) — write 0 where 0 already is (identity)
    # 4. HeadMove(sc, c, d0) — move left: Successor(sc, c) with d0=0
    # 5. TMConfig(c_new, q2, c, tape2')
    # 6. Extend trace
    #
    # This is essentially another phase2-like single step.
    # It's a lot of plumbing but follows the established pattern.

    raise NotImplementedError("phase4 TODO — single step (q1,0)→(0,L,q2)")


if __name__ == '__main__':
    import sys
    sys.setrecursionlimit(100000)
    sys.path.insert(0, '/root/min/src')
    phase4()
