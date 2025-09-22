# B3 documentation

### Reference manual

The B3 reference manual, _This is B3_, is available here at [b3-lang.org](https://b3-lang.org).

It is written in MyST Markdown within Sphinx.

To install:

    pip install sphinx
    pip install myst-parser
    pip install renku-sphinx-theme
    pip install pygments

To build:

    cd doc/refman
    make

To read what you built:

    open doc/refman/_build/html/index.html

### Other documents

* The original [B3 concept document](https://b3-lang.org/krml304.html).

About the implementation:

* [B3 syntax, raw AST, and printing](https://b3-lang.org/krml304.html).

To edit this document, use the [Madoko source](krml304.mdk).
