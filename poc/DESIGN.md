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
expr     = '(' params ')' expr
         | name '(' args ')'
         | name
         | INT
         | STRING
         | '{' let* expr '}'
args     = (expr (',' expr)*)?
params   = (name (',' name)* (',' name '...')? )?
```

`let` always binds `name = expr`. Functions are expressions: `(a, b) body`.
Last parameter may be `name...` — rest parameter, collects into list.
`(` at start of expr = function. `name(` = call. Unambiguous.
