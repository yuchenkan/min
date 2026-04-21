# min (名)

## What this is

A formal problem-solving engine. Given a precise problem description, reason across multiple abstraction levels, produce a correct solution, and prove its correctness. Code generation is the first application.

## Core architecture

- **Engine drives, LLM assists.** The engine owns control flow. LLM is called as a heuristic function when the engine needs to search proof space (suggest proof directions, candidate invariants, lemma choices).
- **Engine provides soundness, LLM provides search.** LLM can be wrong — engine rejects invalid steps. Final correctness depends on engine, not LLM.
- **Three outputs:** spec (what), solution (how), proof (why correct). Spec != program.

## Key decisions

1. High risk, high reward — acknowledged
2. Competitor is code gen tools (Copilot etc), not testing tools
3. Can't just wrap LLM around Z3 — need cross-abstraction reasoning, not single-level tools
4. Spec review: human intervenes for critical problems, auto for routine
5. Not just critical code, not just code — general problem solving
6. People accept errors because they have no choice
7. No fake milestones — research pace
8. Brain uses one mechanism for all abstraction levels — biological precedent
9. Formalized knowledge database is an asset even if engine is slow to develop
10. AI = symbolic + connectionist, not separate. LLM + formal engine is the complete form
11. LLM may already be highly intelligent — needs guidance and verification
12. LLM provides unprecedented heuristic for proof search — this is why NOW is feasible
13. LLM can't improve reasoning without a verifier — we ARE the verifier

## Tech stack

- Python (prototyping speed, swap to systems language later if needed)
- No dependencies yet — pure Python + mock LLM
- LLM integration via anthropic SDK later (needs API key)
- For now: Claude Code as proxy for LLM calls during development

## Theory foundation

- Proof theory + model theory: consistency across abstraction levels
- Set theory: underlying framework for representing objects across levels
- Meta-logic: reasoning about formal systems from outside — the overarching method

## Founder background

- Infrastructure engineer: NetEase game engine, startup infra, Alibaba Cloud storage
- Paxos study -> realized engineering methods are fundamentally insufficient
- Years of mathematical logic research driven by this engineering question
- Book: 数理逻辑与软件工程导论 (219 pages written, theory chapters complete)
- Companion doc: 名 (ming) — roadmap/prospectus

## Project structure

- /vol/formal/bp/ — business plan (LaTeX, git tracked)
- /vol/formal/formal-main.pdf — the book
- /vol/formal/formal.tar.gz — book LaTeX source
- /vol/formal/ming/ — roadmap document + legacy book source
- /root/min/ — this project, the engine
