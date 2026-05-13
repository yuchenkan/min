"""Phase 4+5 combined: two TM steps from P3(b) to TMHalts.

Phase 4: (q1, sc, tape2) --read 0--> (q2, c, tape2)  [move left]
Phase 5: (q2, c, tape2) --read ?--> (qH, sc, tape3)   [write 0, move right, halt]

Combined output: TMHalts(delta, c0, qH, n) where n = S(S(sc)) = S(S(S(c))).
"""

# This is going to be substantial. Let me first understand what needs to happen:
#
# P3(b) gives us: tape2, tra, cj, sc with:
#   TapeUpdate(tape2, tape_in, a, one)
#   Plus(sa, b, sc)
#   Function(tra)
#   dom_bound(tra, sc)
#   TMConfig(cj, q1, sc, tape2)
#   base(tra, z, c0)
#   Apply(tra, sc, cj)
#   step_valid(tra, sc)
#
# We need TMHalts(delta, c0, qH, n) which needs:
#   ∃trace. base(trace,0,c0) ∧ step_valid(trace,n) ∧ trace(n) has state qH
#
# The trace from P3(b) covers 0..sc with sc+1 entries.
# Phase 4 adds step at sc: TMStep(delta, cj, cj4) where cj4 = Config(q2, c, tape2)
# Phase 5 adds step at S(sc): TMStep(delta, cj4, cj5) where cj5 = Config(qH, S(c), tape3)
#
# We extend the trace twice using phase1_step_extend_trace.
# n = S(S(sc)).
#
# This is doable but very long (~500 lines). Let me just outline the key steps.

print("phase45: outline only, not implemented yet")
