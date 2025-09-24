# General syntax

There are two kinds of comments in B3.
A single-line comment starts with `//` and go to the end of the line (ignoring any `/*` that may be found there).
A long comment starts with `/*` and goes until a matching `*/` (or end-of-file, which implicitly closes all
comments). Long comments can be nested.

Statements and expressions are self-terminating, so there are no semi-colons in B3.
Following that style, there is no punctuation between the header (i.e., bound variables, etc.)
and the body of let expressions and quantifier expressions.

The order of top-level declarations is irrelevant as far as referring to other symbols goes.
However, the order of declarations affects the order in which SMT declarations are generated.
