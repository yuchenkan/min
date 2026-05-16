"""TMReachesCompose: chain two TMReaches via trace concatenation.

TMReaches(d,x,a,y) ∧ TMReaches(d,y,b,z) ∧ Plus(a,b,n) → TMReaches(d,x,n,z)

Combined trace: trace3(k) = trace1(k) for k∈a∪{a}, trace3(a+j) = trace2(j) for j∈b∪{b}
where trace1 comes from the first TMReaches and trace2 from the second.

trace3 = {⟨k,v⟩ : k∈S(a) ∧ v=trace1(k)} ∪ {⟨a+j,v⟩ : j∈S(b) ∧ v=trace2(j)}

Actually simpler: for the TMReaches conclusion, we just need:
1. ∃trace3. base(trace3,x) — trace3(0)=x
2. step_valid(trace3,n) — for k<n, trace3 has valid TMSteps
3. Apply(trace3,n,z) — trace3(n)=z

We can build trace3 by extending trace1 with trace2's entries shifted by a.
This is similar to phase1_step_extend_trace but extended b times.

Actually, a simpler approach: prove by induction on b.
Base b=0: n=a. TMReaches(d,x,a,y). TMReaches(d,y,0,z) means y=z (0 steps). So TMReaches(d,x,a,z).
Step b→S(b): TMReaches(d,y,S(b),z). Open: trace2 with trace2(S(b))=z, TMStep at step b.
  By IH: TMReaches(d,x,a+b,z') for some z'. Then one more TMStep from z' to z.
  
Hmm, this requires decomposing TMReaches which is complex.

Simpler approach: just combine the two traces directly.
trace3(k) for k≤a: trace3(k) = trace1(k). Valid because trace1 has valid steps for k<a.
trace3(a+j) for j≤b: trace3(a+j) = trace2(j). Valid because trace2 has valid steps for j<b.
At k=a: trace3(a) = trace1(a) = y = trace2(0). This is the junction point.

The step_valid for trace3 at k where k<n=a+b:
- If k<a (k∈a): trace3(k)=trace1(k), trace3(S(k))=trace1(S(k)), TMStep from trace1. ✓
- If k=a: trace3(a)=trace1(a)=y=trace2(0), trace3(S(a))=trace3(a+1)=trace2(1).
  TMStep: from trace2's step_valid at j=0. ✓ (if trace2(0)=y and trace2(1)=..., TMStep(d,y,...))
- If k>a, k<n: k=a+j where 0<j<b. trace3(k)=trace2(j), trace3(S(k))=trace2(S(j)).
  TMStep from trace2's step_valid at j. ✓

Building trace3 as a set: trace3 = {⟨k,trace1(k)⟩ : k∈S(a)} ∪ {⟨a+j,trace2(j)⟩ : j∈S(b) ∧ j≠0}
Wait, at j=0: a+0=a, and trace1(a) should equal trace2(0). So we don't need j=0 from trace2 
(it's already covered by trace1 at k=a). But we DO need trace2(0) = trace1(a) = y.

This is getting complex. The formal construction requires:
1. Build trace3 via Separation on trace1 ∪ shifted_trace2
2. Prove Function(trace3)
3. Prove base: trace3(0) = trace1(0) = x
4. Prove reached: trace3(n) = trace2(b) = z
5. Prove step_valid: case split on k<a vs k≥a

This is probably 300+ lines. Given the session, let me just try the cleanest approach.

Actually, looking at this more carefully: TMReaches for 0 steps means trace(0)=c0 and trace(0)=cf, so c0=cf (via func_unique). This means TMReaches(d,y,0,z) gives y=z. Then TMReaches(d,x,a,y) becomes TMReaches(d,x,a,z).

But we need Plus(a,b,n). If b=0, n=a. So TMReaches(d,x,n,z) = TMReaches(d,x,a,z). We just need to transfer y→z in the first TMReaches. This is the base case of the b-induction.

For the step case: TMReaches(d,y,S(b'),z). This means trace2 exists with b'+1 steps.
trace2(0)=y, trace2(S(b'))=z, and TMStep at each step. 
The last step: TMStep(d,trace2(b'),z). And trace2(b')=some config c'.
By IH (with b'): TMReaches(d,x,a+b',c'). Then one more TMStep: TMReaches(d,x,a+b'+1,z)=TMReaches(d,x,n,z).

This induction approach avoids building a combined trace from scratch — instead it extends the first trace one step at a time using trace2's steps. This is essentially what phase1_step_extend_trace does!

Actually the cleanest: omega induction on b with:
P(b) = TMReaches(d,y,b,z) → Plus(a,b,n) → TMReaches(d,x,n,z)

Base b=0: TMReaches(d,y,0,z) → y=z. Plus(a,0,n) → n=a. TMReaches(d,x,a,y)=TMReaches(d,x,n,z). ✓
Step: P(b') → P(S(b')). TMReaches(d,y,S(b'),z). Open trace2.
  trace2(b')=c'. TMStep(d,c',z). TMReaches(d,y,b',c') (sub-trace of trace2).
  By IH: Plus(a,b',m) → TMReaches(d,x,m,c'). Then extend by TMStep(d,c',z).
  Plus(a,S(b'),n) and Plus(a,b',m) → m+1=n via plus arithmetic.
  TMReaches(d,x,m,c') extended by one TMStep → TMReaches(d,x,S(m),z) = TMReaches(d,x,n,z).

Hmm, this step case still requires extending a TMReaches by one TMStep. That's essentially tmstep_to_reaches composed with the existing TMReaches. This composition is... what we're trying to prove!

OK, the most direct approach: build the combined trace as a set. Use Separation to define trace3 = {p : (∃k∈S(a). p=⟨k,trace1(k)⟩) ∨ (∃j. 0<j ∧ j∈S(b) ∧ ∃pos. Plus(a,j,pos) ∧ p=⟨pos,trace2(j)⟩)}.

This is very complex. Given time constraints, let me just write the omega induction approach since we have the machinery.

Actually, the simplest approach of ALL: use phase1_step_extend_trace in a LOOP. TMReaches(d,x,a,y) gives a trace of a steps. TMReaches(d,y,b,z) gives trace2 with b steps. I extend the first trace by each step of trace2, one at a time, via omega induction on b.

The induction predicate: Q(j) = "there exists a trace of a+j steps from x, ending at trace2(j)".
Base j=0: trace2(0)=y. Trace of a steps from x ending at y = TMReaches(d,x,a,y). ✓
Step: Q(j)→Q(S(j)). Trace of a+j steps from x ending at trace2(j)=c'. 
  trace2's step_valid at j: TMStep(d,c',trace2(S(j))). 
  Extend trace by one: trace of a+j+1 = a+S(j) steps from x ending at trace2(S(j)). ✓

At j=b: Q(b) = trace of a+b=n steps from x ending at trace2(b)=z = TMReaches(d,x,n,z). ✓

This is clean but requires opening TMReaches(d,y,b,z) to get trace2's step_valid, and using it inside the induction. The induction carries the extended trace (like Phase1Ind).

This is still 200+ lines. Let me just start coding it.
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
from tactics import apply_thm, mp, ax, fl, eir, eel, cut, wl, wr, weaken_to

# For now, just test that the vocab works
if __name__=='__main__':
    from theorems.tm import TMReachesCompose
    g=TMReachesCompose()
    print(f'TMReachesCompose: {str(g.expand())[:120]}')
    print(f'same(g,g)? {same(g,g,expand=False)}')


# TODO: implement tmreaches_compose
# Strategy: omega induction on b, extending trace by one TMStep at each step.
# Reuses phase1_step_extend_trace.
# This will be ~250 lines following the phase1/phase3 pattern.
