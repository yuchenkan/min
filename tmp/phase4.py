def phase4():
    """Phase 4: (q1, sc) → (q2, c) moving left. Single TM step.

    Takes P3(b) + transitions. Extends trace by one step.
    Output: trace with TMConfig(_, q2, c, tape2) at position S(sc).

    Hypotheses: Phase3P(b,...), TMTransition(delta,q1,zero,zero,d0,q2),
    Plus(sa,b,sc), Successor(sc,c), Num(d0,0), Num(zero,0), Num(q2,3),
    Omega(w), In(c,w), In(sc,w), Function(delta), Function(tape_in),
    Successor(sa,a), UnaryTape(tape_in,a,b)."""

    # Phase4 is structurally similar to phase3_step but:
    # 1. Reads 0 (not 1) at position sc via tape_read_end + tape_update_other/LEM
    # 2. Moves LEFT (d0=0, HeadMove uses Successor(sc,c) with Or right branch)
    # 3. Transition to q2 (not staying in q1)
    # 4. No Plus advancement (single step, not induction)
    #
    # For TMStep: trivial ∀ packaging. Just need cfg2 = TMConfig(cj_new, q2, c, tape2).
    # For trace extension: phase1_step_extend_trace.
    #
    # Output structure: similar to P3 but at position S(sc) with state q2.
    # Actually, for TMHalts we just need the trace function + final config.
    # Let me produce something compatible with the next phase.

    raise NotImplementedError("phase4 TODO")


if __name__ == '__main__':
    import sys
    sys.setrecursionlimit(100000)
    sys.path.insert(0, '/root/min/src')
    phase4()
