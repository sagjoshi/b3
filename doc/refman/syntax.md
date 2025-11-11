# General syntax

## Comments

There are two kinds of comments in B3.
A single-line comment starts with `//` and goes to the end of the line (ignoring any `/*` that may be found in between).
A long comment starts with `/*` and goes until a matching `*/` (or end-of-file, which implicitly closes all
comments). Long comments can be nested, but single-line comments are not supported inside long comments.

```{literalinclude} ../../test/refman/syntax.b3
:start-after: // BEGIN Comments
:end-before: // END Comments
```

## Self-terminating statements and expressions

Statements and expressions are self-terminating, so there are no semi-colons in B3.
Following that style, there is no punctuation between the header (i.e., bound variables, etc.)
and the body of let expressions and quantifier expressions.

```{literalinclude} ../../test/refman/syntax.b3
:start-after: // BEGIN SelfTerminating
:end-before: // END SelfTerminating
```

## Order of declarations

The order of top-level declarations is irrelevant as far as referring to other symbols goes.
However, the order of declarations may affect the order in which a B3 back end generates SMT declarations.

```{literalinclude} ../../test/refman/syntax.b3
:start-after: // BEGIN DeclarationOrder
:end-before: // END DeclarationOrder
```
