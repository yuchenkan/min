# Language Design

## 1. Pure functional

No loops, no mutation, no side effects.
Recursion replaces loops. Everything is an expression.

## 2. Computation traces

Every `let name = expr` binding records its AST.
`repr(ast)` reconstructs the source. Display at any depth.

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
expr     = '[' params ':' expr ']'
         | '?' '(' expr ',' expr ',' expr ')'
         | '{' let* expr '}'
         | expr '(' args ')'
         | name
         | INT
         | STRING
args     = (expr (',' expr)*)?
params   = (name (',' name)* (',' name '...')? )?
```

`let` always binds `name = expr`. Functions are expressions: `[a, b : body]`.
`[` opens function, `:` separates params from body, `]` closes — no ambiguity.
Any expression can be called: `f(1)(2)` = chained calls.
Call holds callee expr, not just name.
Last parameter may be `name...` — rest parameter, collects into list.
Zero-param function: `[: body]`.
`?(cond, then, else)` — special form, lazy branches. Not a function, not assignable.
