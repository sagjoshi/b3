# Top-level declarations

A _program_ consists of a list of top-level declarations. The order of these is irrelevant.

```
Program ::=
  | TypeDecl
  | Tagger
  | Function
  | Axiom
  | Procedure
```

## Types

```
TypeDecl ::=
  type Identifier
```

A declaration `type A` declares `A` to be a nonempty but otherwise uninterpreted type.

There are three built-in types, `bool`, `int`, and `tag`. The use of a type is therefore

```
Type ::=
  | bool
  | int
  | tag
  | Identifier
```

(sec-taggers)=
## Taggers

```
Tagger ::=
  tagger Identifier for Type
```

A _tagger_ is a special function from the given type to a `tag`. The declaration `tagger G for A`
has the effect of declaring a function

```
function G(subject: A): tag
```

This function is available for use like any other function in the program.

What makes a tagger special is that it can be mentioned in the `tag` clause of other function
declarations, see {ref}`sec-function-tags`.

## Functions

```
Function ::= 
  function Identifier "(" FParameter*, ")" ":" Type [ tag Identifier ]
  [
    ( when Expression )*
    "{" Expression "}"
  ]

FParameter ::=
  [ injective ] Identifier ":" Type
```

A declaration `function F(x: X): Y` declares a function from `X` to `Y`.

* The names of the function's parameters must be distinct.
* The name of the function itself must not be the same as any other function or tagger.
* The identifier in the optional `tag` clause must denote a tagger.
* Any `when` expression must have type `bool`, and
  the type of the optional body expression (between curly braces) must be
  function's result type.
* The free variables of the `when` expressions and body can be any subset of the
  function's parameters.

### Function definition

A function can be given a definition by providing a body. For example:

```{literalinclude} ../../test/refman/top-level-decls.b3
:start-after: // BEGIN Double
:end-before: // END Double
```

Such a definition has the effect of declaring an axiom

```{literalinclude} ../../test/refman/top-level-decls.b3
:start-after: // BEGIN DoubleAxiom
:end-before: // END DoubleAxiom
```

but better retains the intent behind such an axiom. For example, a B3 back end may give better error diagnostics
if the definition is associated with the function.

### Underspecified functions

Functions in B3 are total. However, a function may be underspecified. Then `when` clause is used to give the
condition under which the body applies. For example,

```{literalinclude} ../../test/refman/top-level-decls.b3
:start-after: // BEGIN Underspecification
:end-before: // END Underspecification
```

defines `Decrease` for positive integers and leaves it uninterpreted for non-positive integers, as would
be stated by the axiom

```{literalinclude} ../../test/refman/top-level-decls.b3
:start-after: // BEGIN UnderspecificationAxiom
:end-before: // END UnderspecificationAxiom
```

### Functions that are injective in their arguments

Many functions are injective in one or more of their arguments. This can be indicated in a function
declaration by preceding a parameter with `injective`. For example, if `GPSPoint` and `string` are types, then

```{literalinclude} ../../test/refman/top-level-decls.b3
:start-after: // BEGIN Injective
:end-before: // END Injective
```

says that `MapCoordinate` is injective in each of its first two parameters. Consequently, the first
check condition in the following program snippet is provable:

```{literalinclude} ../../test/refman/top-level-decls.b3
:start-after: // BEGIN InjectivityConsequences
:end-before: // END InjectivityConsequences
```

whereas injectivity alone is not enough to determine which of the second and third conditions holds.

A function `F` declared to be injective in one of its parameters `x` automatically introduces the
corresponding inverse function, named `F..x`. That is, the declaration of `MapCoordinate` above also
introduces the functions

```
function MapCoordinate..x(subject: GPSPoint): int
function MapCoordinate..y(subject: GPSPoint): int
```

with the associated axioms

```
axiom explains MapCoordinate
  forall x: int, y: int, label: string
    pattern MapCoordinate(x, y, label)
    MapCoordinate..x(MapCoordinate(x, y, label)) == x

axiom explains MapCoordinate
  forall x: int, y: int, label: string
    pattern MapCoordinate(x, y, label)
    MapCoordinate..y(MapCoordinate(x, y, label)) == y
```

```{note}
User-defined identifiers are not allowed to contain the substring `..`, so the names of these automatically
generated inverse functions are unique.
```

````{note}
A semantically equivalent way of axiomatizing injectivity for `MapCoordinate` is

```{literalinclude} ../../test/refman/top-level-decls.b3
:start-after: // BEGIN ManualInjectivity
:end-before: // END ManualInjectivity
```

However, this axiomatization gives rise to poor SMT performance because the number of matches for its pattern
is quadratic is the number of `MapCoordinate` terms in the proof context. It's better to mark parameters
with `injective`, whether or not the inverse functions are used elsewhere in the B3 program.
````

(sec-function-tags)=
### Functions with disjoint images

Sometimes, two functions, say `F` and `G`, have the property that their functional images are disjoint.
In other words, the values returned by `F` are never the same as the values returned by `G`. A group of
functions can be declared to pairwise have this behavior. This is done by associating a {ref}`tagger <sec-taggers>`
with each of the functions in the group.

For example, the program snippet

```{literalinclude} ../../test/refman/top-level-decls.b3
:start-after: // BEGIN Tagger
:end-before: // END Tagger
```

declares three `Drink` functions, `Coffee`, `Tea`, and `SoftDrink`. By also declaring the tagger `Variety` and
declaring the functions with `tag Variety`, these declarations say that functions `Coffee`, `Tea`, and `SoftDrink`
return disjoint values. That is, `Coffee(x)` is not equal to `Tea(y)` and not equal to `SoftDrink(z)`, regardless
of the values of the arguments `x`, `y`, and `z`.

The effect of a `tag` clause on a function `F` is to declare an additional function, `F..tag`. So, for `Coffee`,
the function is

```
function Coffee..tag(): tag
```

B3 arranges for all such `F..tag` functions to return distinct values (across all names of taggers). Hence, the
condition

```{literalinclude} ../../test/refman/top-level-decls.b3
:start-after: // BEGIN TagsAreDifferent
:end-before: // END TagsAreDifferent
```

holds. The result values of `F` and "tagged" with the value `F..tag()`. More precisely, `F`'s tagger function
returns `F..tag()` when applied to the result values of `F`. Applied to the `Drink` example, we have

```{literalinclude} ../../test/refman/top-level-decls.b3
:start-after: // BEGIN TagAxiom
:end-before: // END TagAxiom
```

````{note}
The combination of `injective` and `tag` are useful in declaring what essentially are the constructors of
algebraic datatypes. For example, to represent a type like

    datatype List = Nil() | Cons(head: int, tail: List)

from another programming language, one can in B3 declare

```{literalinclude} ../../test/refman/top-level-decls.b3
:start-after: // BEGIN Datatype
:end-before: // END Datatype
```

````

### Inconsistent function definitions

It is possible to declare a function body that gives rise to a logical inconsistency.
For example, the declaration

```{literalinclude} ../../test/refman/top-level-decls.b3
:start-after: // BEGIN InconsistentFunction
:end-before: // END InconsistentFunction
```

allows one to conclude `Bad(100) == 1 + Bad(100)`, which is `false`.

Logical inconsistencies can also arise from a combination of a body and the `injective` or `tag`.
For example,

```{literalinclude} ../../test/refman/top-level-decls.b3
:start-after: // BEGIN InconsistentFunctionMarkup
:end-before: // END InconsistentFunctionMarkup
```

would let one conclude

```{literalinclude} ../../test/refman/top-level-decls.b3
:start-after: // BEGIN InconsistentFunctionMarkupTest
:end-before: // END InconsistentFunctionMarkupTest
```

which also implies `false`.

The B3 language itself does not forbid declarations like the above that cause logical inconsistencies
(but third-party tools might try to detect them).
The reason for not forbidding them is to allow a source language to encode its proof obligations into B3
without first having to detect the inconsistencies; if the source language is concerned with such
inconsistencies, then it would encode additional proof obligations in B3 that detect the source-language
inconsistencies. The `explains` clauses of `axiom`s in B3 allow these two encodings to be done simultaneously.

## Axioms

```
Axiom ::=
  axiom [ explains Identifier+, ]
    Expression
```

The `explains` clause names a set of functions.
The axiom is added to the antecedent of a proof obligation if all of the functions have been included in the proof obligation.

## Procedures

```
Procedure ::=
  procedure Identifier "(" PParameter*, ")"
    Spec*
  [ BlockStmt ]

PParameter ::=
  [ inout | out ] Identifier ":" Type [ autoinv Expression ]

Spec ::=
  | requires AExpression
  | ensures AExpression

AExpression ::=
  | Expression
  | BlockStmt
```

There are restrictions on the `BlockStmt` version of `AExpression` as to which statements the block
is allowed to contain.

There are three parameter modes: in, inout, and out. The absence of `inout` and `out` indicates an
in-argument.

In the procedure body, in-parameters are immutable and inout- and out-parameters are mutable.