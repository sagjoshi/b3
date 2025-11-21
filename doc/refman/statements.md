# Statements

```
Stmt ::=
  | VarDecl
  | Assign
  | Reinit
  | BlockStmt
  | Call
  // assertions
  | Check
  | Assume
  | Reach
  | Assert
  | AForall
  // control flow
  | Choose
  | If
  | IfCase
  | Loop
  | LabeledStmt
  | Exit
  | Return
  // error reporting
  | Probe
```

The _scope_ of a statement determines which free variables the statement may use.
The scope typically includes the parameters of the enclosing procedure. It also includes
local variables, according to standard lexical-scope rules. The variables in a scope
are either mutable, which allows their values to be changed by statements, or immutable.
A procedure's in-parameters are immutable, whereas inout- and out-parameters are mutable.

`````{note}
Statements and expressions in B3 are self-terminating, so there are no semi-colons.
`````

`````{note}
In the reference implementation of B3, parsing gives a _raw_ AST, which is then processed into a _resolved_ AST.
The resolved AST is structured slightly differently than the raw AST that corresponds to the surface syntax.
For more information, see these [developer notes](https://b3-lang.org/krml304.html).
`````

## Variable declarations

```
VarDecl ::=
  ( var | val ) Identifier [ ":" Type ] [ "autoinv" Expression ] [ ":=" Expression ]
```

A declaration `var x: T := e` introduces a mutable local variable of type `T` and initial
value `e`, and `val x: T := e` introduces an immutable local variable with value `e`.

The variable declaration is allowed to omit one of `: Type` or `:= Expression`,
but not both. If the type is omitted, it is determined from the given expression.
If the expression is omitted, the variable is initialized with an arbitrary value
of its type.

A mutable variable that is never updated is semantically equivalent to an immutable variable.
However, the body of a {ref}`forall statements <sec-forall-stmt>` is not allowed to declare
mutable variables.

The variable remains in scope until the end of the enclosing block.

A variable is allowed to shadow previously declared variables with the same name. Doing so makes the
previous variable with that name inaccessible until the shadowing variable goes out of scope.

The optional `autoinv e` clause associates an auto-invariant with the variable. The expression `e`
must have type `bool` and can mention any variable in scope, including the variable being introduced.
For a description of auto-invariants, see {ref}`sec-autoinv`.

## Assignment statements

```
Assign ::=
  Identifier ":=" Expression
```

The statement `x := e` evaluates expression `e` and then sets variable `x` to have that value.

The identifier must be a mutable variable. The type of the RHS expression must be the same as the
type of the LHS variable.

## Re-init statements

```
Reinit ::=
  reinit Identifier+,
```

The statement `reinit x, y, z` sets the variables `x`, `y`, and `z` to arbitrary values of their types.

Each of the given identifiers must denote a mutable variable in scope.
The list of variable is allowed to contain duplicates, but the effect of the statement is the same as
if the duplicates are removed.

## Block statements

```
BlockStmt ::=
  "{" Stmt* "}"
```

A block statement introduces a scope. Variables declared inside the block statement remain in scope until the end
of the block.

## Call statement

```
Call ::=
  Identifier "(" CallArgument ")"
CallArgument ::=
  | Expression
  | ( "inout" | "out" ) Identifier
```

A call statement `call P(e, inout y, out z)` invokes procedure `P`, passing it the value of `e` as an in-parameter,
variable `y` as an inout-parameter, and variable `z` as an out-parameter.

For readability, the parameter mode (in, inout, or out) of each argument is explicitly repeated at the call site[^fn-mode-at-call-site]
(where the absence of `inout` and `out` indicates an in-argument).

[^fn-mode-at-call-site]: following C#

The types of the actual arguments must be the same as for the corresponding formal parameters.

The variables given as inout- and out-arguments must be distinct mutable variables.

It is an error if a program trace reaches the call statement and one of the callee's preconditions does not hold.
Nevertheless, a program trace proceeds into the call even if some precondition does not hold. For a deductive
verifier, this is the "check and forget" semantics.

## Check statements

```
Check ::=
  check Expression
```

The statement `check e` declares the intention that every program trace leading to
this statement find `e` to evaluate to `true`.
It is an error if a program trace reaches the statement and `e` evaluates to `false`.

The given expression must have type `bool`.

A program trace continues after the `check` statement even if the condition does not hold. For a
deductive verifier, this is the "check and forget" semantics.

## Assume statements

```
Assume ::=
  assume Expression
```

The statement `assume e` declares that a program trace leading to this statement is of interest
only when `e` evaluates to `true`. In other words, the `assume` statement says that
"what follows this statement is relevant only if `e` evaluates to `true`".

The given expression must have type `bool`.

## Reach statements

```
Reach ::=
  reach Expression
```

The statement `reach e` declares the intention that there exist a program trace that leads to
this statement and finds `e` to evaluate to `true`.

The given expression must have type `bool`.

## Assert statements

```
Assert ::=
  assert Expression
```

A statement `assert e` is equivalent to the statement sequence `check e assume e`.

The given expression must have type `bool`.

(sec-forall-stmt)=
## Forall statements

```
AForall ::=
  forall Identifier ":" Type
  BlockStmt
```

TODO: description

## Choose statements

```
Choose ::=
  choose BlockStmt ( or BlockStmt )*
```

A statement `choose S or S'` arbitrarily chooses one of the alternatives `S` and `S'` and proceeds as it.
In other words, the `choose` statement gives rise to the union of the program traces of each of its components.

## If statements

```
If ::=
  if Expression BlockStmt [ else IfContinuation ]
IfContinuation ::=
  | BlockStmt
  | If
  | IfCase
```

The statement

```
if e
  S
else
  S'
```

chooses `S` or `S'` depending on the value of `e`. In particular, it chooses `S` if `e` evaluates to `true`
and otherwise chooses `S'`.

The expression must have type `bool`.

If an explicit `else` branch is omitted, it defaults to `else { }`.

The three variations of `IfContinuation` gives a streamlined syntax for writing cascading `if` statements, but
are semantically equivalent to putting the `If` or `IfCase` inside a block statement.





TODO: give an example of how to encode a `match` statement using `val` and an `if` (where each `else` uses quantifier
to say there's no value for the previous bound variables).

## If-case statements

```
IfCase ::=
  if Case+
Case ::=
  case Expression BlockStmt
```

The statement

```
if
case e0 S0
case e1 S1
case e2 S2
```

chooses a `case` alternative whose expression evaluates to `true` and then proceeds as the corresponding
statement body. It also declares that a program trace leading to this if-case statement is of interest only
when at least one of the `case` expressions evaluates to `true`.

Each expression must have type `bool`.

The `case`s are unordered. If the expression for more than one `case` evaluates to `true`, the statement
arbitrarily chooses one of them.

If no `case` evaluates to `true`, then the entire statement is like `assume false`.

(sec-loops)=
## Loops

```
Loop ::=
  loop Invariant* BlockStmt
Invariant ::=
  invariant AExpression
```

A loop statement

```
loop
  invariant e
Body
```

checks the condition `e` (like a `check e`) and then proceeds as `Body`. If a trace reaches the end
of `{ Body }`, it proceeds as the entire loop statement. Stated differently, the loop statement repeatedly
proceeds as `Body`, checking condition `e` before each such iteration, and ending only if an
iteration of `Body` ever exit abruptly (with an `exit` or `return`).

Expression `e` is called a _loop invariant_ because it declares the intention that `e` hold at the
top of every iteration of `Body`.

`````{admonition} Example
:class: tip
A loop `while b { Body() }` commonly found in programming languages is encoded in B3 as

```{literalinclude} ../../test/refman/statements.b3
:start-after: // BEGIN While
:end-before: // END While
```

A loop `do { Body() } while b` is encoded as

```{literalinclude} ../../test/refman/statements.b3
:start-after: // BEGIN DoWhile
:end-before: // END DoWhile
```

`````

## Labeled statements

```
LabeledStmt ::=
  Identifier ":" ( BlockStmt | Loop )
```

A loop or block statement `S` can be given a name `lbl` by writing `lbl: S`.
Such a label provides a way to abruptly exit statement `S` by name. More precisely,
`lbl: S` proceeds as `S`, but if `S` exits abruptly to label `lbl`, then `lbl: S`
continues normally.

In other words, `lbl: S` is like an empty "exception handler" for `lbl` in `S`.

A label is not allowed to shadow another label. That is, in `lbl: S`, statement
`S` is not allowed to use `lbl` as a label. It is, however, legal to reuse the
same label name in non-nested ways; for example,

```
lbl: S
lbl: S'
```

is legal.

## Exit statements

```
Exit ::=
  exit [ Identifier ]
```

A statement `exit lbl` instigates an abrupt exit. This causes a program trace to
continue immediately after the enclosing statement labeled with `lbl`.

The given identifier must be a label name in scope. That is, `exit lbl` can only
be used inside a statement `S` in a labeled statement `lbl: S`.

If the `exit` statement is placed in the body of a (labeled or unlabeled) loop, then
the label identifier can be omitted. This causes the abrupt exit to continue immediately
after the most tighly enclosing (labeled or unlabeled) loop. This is especially
useful when encoding common `while` loops, see {Ref}`sec-loops`.

`````{admonition} Example
:class: tip
The `continue` statement found in many programming languages can be encoded by labeling the
body of a loop. For example, a loop like

```{code-block} text
:class: italic-code
while b {
  Stmt0()
  if c {
    continue
  }
  Stmt1()
}
```

is encoded as

```{literalinclude} ../../test/refman/statements.b3
:start-after: // BEGIN Continue
:end-before: // END Continue
```

`````

`````{admonition} Example
:class: tip
Exception handling can also be encoded using labels and exists. For example, consider a program

```{code-block} text
:class: italic-code
try {
  Stmt0()
  if c {
    throw Unexpected
  }
  Stmt1()
} catch Unexpected {
  Handler()
}
```

Here, the handler for the `throw` statement can be determined lexically. This can be encoded
in B3 as

```{literalinclude} ../../test/refman/statements.b3
:start-after: // BEGIN LexicExceptionHandling
:end-before: // END LexicExceptionHandling
```

In the more common case, where a handler is not in the same lexical scope as the `throw`, use an
out-parameter to communicate if a procedure returns normally or exceptionally, and if so, with
which exception. Then, inspect this variable after each call and follow the template above to
transfer control to the enclosing exception handler. If there is no lexically enclosing exception
handler, set the out-parameter and abruptly return (using `return`) from the procedure.

`````

## Return statements

```
Return ::=
  return
```

A `return` statement exits a procedure body abruptly. This transfers control out
of the enclosing procedure body, at which point the procedure's postconditions are checked.

A `return` statement can only be used in a procedure body. For example, it cannot be used inside
an `AExpression`.

## Probe statements

```
Probe ::=
  probe Expression
```

A statement `probe e` has no effect in a trace. It is used to record the value of expression `e`, in
the event that an error is reported along a trace that passes through the probe statement. In this
way, the `probe` statement is a bit like a debug print statement.[^fn-boogie-print]

[^fn-boogie-print]: Indeed, the `probe` statement is similar to Boogie's `print` statement.

The type of the expression must be `bool`.
