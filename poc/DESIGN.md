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
program  = (import | bind)*
import   = 'from' dotted_name 'import' names
bind     = '=' '(' name expr ')'
expr     = '*' '(' params ':' expr ')'
         | '[' (expr (',' expr)*)? ']'
         | '?' '(' expr ',' expr ',' expr ')'
         | '{' bind* expr '}'
         | expr '(' (expr (',' expr)*)? ')'
         | name
         | INT
         | STRING
params   = name*
```

`=(name expr)` bind. `*(a b : body)` function. `f(x, y)` call.
`[1, 2, 3]` list. `?(cond, then, else)` conditional.
No commas in binds and params.
