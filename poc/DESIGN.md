# Language Design

## 1. Pure functional language

No loops, no mutation, no side effects.
Recursion replaces loops. Everything is an expression.
This is inviolable.

## 2. Everything is an object

1 is an object. "str" is an object. Functions are objects.
No primitives vs objects distinction. Uniform treatment.

## 3. Every object carries its computation trace

Every value records how it was computed: function name + arguments.
This is immutable metadata, not side effect.
Display at any depth: trace name → one step → full expansion.
Wrap/provenance is first-class, not bolted on.

## 4. Garbage collection

Traces and objects accumulate. GC reclaims unreferenced objects.
Pure functional = no mutation = no dangling references = GC-safe.
If an object is unreachable, its trace is also unreachable — collect both.

## 5. Builtin types

- Int — integers
- Bool — True/False
- String — text
- Pair — the only compound type. fst/snd for access.
  All structured data built from nested pairs. No dots.

## 6. Everything is a function call

Uniform syntax: Name(args). No operators, no infix.
if(cond, a, b), add(1, 2), Pair(a, b) — all function calls.
Parsing is trivial — one syntax rule.

## 7. Strict evaluation, lazy branches

Strict by default — expressions evaluate immediately.
if(cond, a, b) is lazy — only evaluates chosen branch.
No thunks, no auto-calling.

## 8. Bindings and functions

x = expr — binding, evaluated immediately.
f(a, b) = body — function, evaluated when called.
No mutation — once bound, x never changes.

## 9. Top level

A file contains only imports and bindings.
No bare expressions. No side effects at top level.
