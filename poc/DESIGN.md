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
