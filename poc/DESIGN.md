# Language Design

## 1. Pure functional

No loops, no mutation, no side effects.
Recursion replaces loops. Everything is an expression.

## 2. Computation traces

Every function call records (fn, args, result).
Display at any depth for debugging.

## 3. Everything is a function call

Uniform syntax: Name(args). No operators, no infix.
Parsing is trivial — one syntax rule.

## 4. Strict evaluation, lazy branches

Strict by default — expressions evaluate immediately.
if(cond, a, b) only evaluates chosen branch.

## 5. Syntax

```
program  = (import | let)*
import   = 'from' dotted_name 'import' names
let      = 'let' name '=' expr
         | 'let' name '(' params ')' '=' expr
expr     = name '(' args ')'
         | name
         | INT
         | STRING
         | '{' let* expr '}'
args     = (expr (',' expr)*)?
params   = (name (',' name)* (',' name '...')? )?
```

`let` keyword marks all bindings. No ambiguity:
- `let name(...)` = function definition (params are bare names)
- `name(...)` in expr = function call (args are expressions)
Last parameter may be `name...` — rest parameter.
Collects remaining args into list.
