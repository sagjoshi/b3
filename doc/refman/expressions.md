# Expressions

Every expression has a type that can be uniquely determined from the expression itself,
provided the expression is well-formed and well-typed.

```
Expression ::=
  | Literal
  | Id
  | OperatorExpr
  | FunctionCall
  | LabeledExpr
  | LetExpr
  | QuantifierExpr
  | "(" Expression ")"
```

## Literal expressions

```
Literal ::=
  | false | true
  | 0 | 1 | 2 | ...
  | "|" LiteralIdentifier ":" Type "|"
```

The literals `false` and `true` have the built-in type `bool`.

Natural numbers have the built-in type `int`. They are unbounded integers.
Negative integers can be formed using the unary-minus operator.

B3 has very few built-in types. For user-defined types, one way to define
specific values is to define a nullary function for each such value, optionally
tagging the functions to indicate that they give distinct values. For example,

```{literalinclude} ../../test/refman/expressions.b3
:start-after: // BEGIN Airport
:end-before: // END Airport
```

or

```{literalinclude} ../../test/refman/expressions.b3
:start-after: // BEGIN real
:end-before: // END real
```

However, when the number of values is large---indeed, perhaps infinite---then
this approach is at best clumsy. To address this issue and yet remain mostly
agnostic about the details of non-built-in types, B3 supports _custom literals_.

A custom literal is an identifier-like token with a given type.
Syntactically, the identifier-like token is just a string of input characters;
B3 does not further parse or interpret this string by itself.
But when the same identifier-like token is used in multiple places for the same type,
B3 interprets them as having the same value. For example, the following is
always provable:

```{literalinclude} ../../test/refman/expressions.b3
:start-after: // BEGIN AirportExample
:end-before: // END AirportExample
```

B3 does not say whether or not two custom literals with different
identifier-like tokens are equal.
That is, in general, neither of the following checks is provable:

```{literalinclude} ../../test/refman/expressions.b3
:start-after: // BEGIN realExample
:end-before: // END realExample
```

Syntactically, a custom literal always includes its type. Custom literals
of different types are allowed to use overlapping sets of identifier-like tokens.

Custom literals can be given more specific interpretations using a
_foreign function interface_, described elsewhere.

## Identifier expressions

```
Id ::=
  [ old ] Identifier
```

The given identifier must denote a variable in scope. Such a variable may be

* an in-, inout-, or out-parameter
* a mutable or immutable local variable
* a bound variable

The type of the expression is the type of the variable.

In postconditions and procedure bodies, the use of an inout-parameter `y` as
an expression refers to the post-state value (in postconditions) or current value
(in bodies) of `y`. In these contexts, it is also possible to refer to the
pre-state value of `y`, that is, the value of `y` on entry to the procedure.
This is written `old y`.

## Operator expressions

```
OperatorExpr ::=
  | if Expression Expression else Expression
  | Expression BinaryOp Expression
  | UnaryOp Expression
BinaryOp ::=
  | "<==>"
  | "==>" | "<=="
  | "&&" | "||"
  | "==" | "!=" | "<" | "<=" | ">=" | ">"
  | "+" | "-"
  | "*" | div | mod
UnaryOp ::=
  | "!" | "-"
```

The ternary operator expression `if b e0 else e1` evaluates to `e0` if `b` evaluates to `true` and
evaluates to `e1` if `b` evaluates to `false`. The type of `b` must be `bool`, and the types of
expressions `e0` and `e1` must be the same.

Binary and unary expressions are parsed according to precedence and associativity rules.
The unary operators have the highest binding power. The following table lists the
binding powers of binary operators, from lowest to highest:

| operators | associativity |
|----------|----------|
| `<==>` | associative |
| `==>`  `<==` | `==>` associates to the right,<br>`<==` associates to the left,<br>the two different operators do not associate with each other |
| `&&`  `\|\|` | associative,<br>the two different operators do not associate with each other |
| `==`  `!=`  `<`  `<=`  `>=`  `>` | not associative |
| `+`  `-` | left associative |
| `*`  `div`  `mod` | left associative |

Here are descriptions of these operators and their type signatures:

| operators | type | description |
|----------|----------|----------|
| `<==>` | `bool` $\times$ `bool` $\to$ `\bool` | boolean equivalence, aka boolean equality, aka "if and only if" |
| `==>`  | `bool` $\times$ `bool` $\to$ `\bool` | logical implication |
| `<==`  | `bool` $\times$ `bool` $\to$ `\bool` | reverse implication (that is, `A ==> B` is the same as `B <== A`) |
| `&&`   | `bool` $\times$ `bool` $\to$ `\bool` | logical conjunction, aka "and" |
| `\|\|` | `bool` $\times$ `bool` $\to$ `\bool` | logical disjunction, aka "or" |
| `==`   | $\alpha \times \alpha \to$ `\bool` | equality |
| `!=`   | $\alpha \times \alpha \to$ `\bool` | disequality, aka "not equal" |
| `<`  `<=`  `>=`  `>` | `int` $\times$ `int` $\to$ `bool` | less, at most, at least, greater |
| `+`    | `int` $\times$ `int` $\to$ `int` | addition |
| `-`    | `int` $\times$ `int` $\to$ `int` | subtraction |
| `*`    | `int` $\times$ `int` $\to$ `int` | multiplication |
| `div`  | `int` $\times$ `int` $\to$ `int` | Euclidean division |
| `mod`  | `int` $\times$ `int` $\to$ `int` | Euclidean modulo |

Notes:

* In the table above, $\alpha$ can be any type, but it has to be the same for both operands.

* The comparison operators are not chaining.[^fn-chaining]

* Like all functions and expressions in B3, `div` and `mod` are total, and in particular they
    give an integer result even when the divisor (the second argument) is `0`. When the divisor is `0`,
    `div` and `mod` each gives a result that is a function of its first argument, but B3 intentionally
    omits any further specification of the value.[^fn-div-mod-underspecified]

* Operators `div` and `mod` use Euclidean division and modulo.
    This is also what Dafny, Boogie, and SMT-LIB use,
    but is different from the _truncated_ division and modulo that, for example, Java and C use.
    See wikipedia for more information about
    Euclidean [division](https://en.wikipedia.org/wiki/Euclidean_division) and [modulo](https://en.wikipedia.org/wiki/Modulo).

[^fn-chaining]: unlike comparison operators in Dafny

[^fn-div-mod-underspecified]: this is also what Boogie and SMT-LIB do

## Function calls

```
FunctionCall ::=
  Identifier "(" Expression*, ")"
```

TODO: description

## Labeled expressions

```
LabeledExpr ::=
  Identifier ":" Expression
```

The `Expression` parses as far as possible.

TODO: description

## Let expressions

```
LetExpr ::=
  val Identifier ":=" Expression Expression
```

Note that there is no punctuation between the two expressions.

TODO: description

## Quantifier expressions

```
QuantifierExpr ::=
  ( forall | exists ) Identifier ":" Type
  Pattern*
  Expression
Pattern ::=
  pattern Expression+,
```

TODO: description
