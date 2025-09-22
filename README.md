# B3

B3 is an _intermediate verification language_ (IVL). Like other IVLs (for example, Boogie 2, Why3, and Viper), B3 provides a natural way to express proof obligations that arise in deductive program verification. More generally, a translation from a programming language into B3 can capture the semantics of that language.

B3 improves on Boogie 2 in two major ways:

* The B3 language is streamlined for the kinds of encoding tasks that the Dafny-to-Boogie translation have developed over a period of 15+ years. For example, B3 has `check` statements ("check and forget"), `injective` modifiers for function parameters, and various "bread crumbs" that can be used to report detailed error messags.

* The B3 verifier is designed, from the ground up, with proof stability in mind. For example, the verifier uses symbolic execution without joins, so the "then" and "else" branches of a condition are never considered together. Any temporary names introduced in that process are generated independently for the two branches. Also, the verifier introduces types, functions, and axioms into the verification context lazily. This reduces the size of the proof context, which experience shows has a positive effect on proof stability.

B3 is implemented in Dafny, so the implementation is scrutinized by the Dafny verifier.

## View and build

To view and edit the sources, open this folder with VS Code.

To manage the project from the command line, see the `Makefile`. For example, to verify the code, run

```
make verify
```

You'll need Dafny version 4.11.

## Test

B3 test depends on [LLVM lit](https://llvm.org/docs/CommandGuide/lit.html) and [OutputCheck](https://pypi.org/project/OutputCheck/). Install them by using the following command and run test suites by `make lit`.

```script
brew install pipx
pipx install lit==18.1.8
pipx install OutputCheck
```

## B3 documentation

The main documentation for B3 is its language reference language, [This is B3](https://b3-lang.org).

The original [B3 concept document](https://b3-lang.org/krml301.html) gives some thinking and motivation. Note, however, that the language has evolved, so the concept document does not always describe what is implemented.

Other documents for B3 contributors are available in the [`doc` folder](doc).

## Tool stages

- `Parser`: input characters -> raw AST
  -- `RawAst.WellFormed` says whether or not raw AST is well-formed, but doesn't give good error messages
- `Resolver`: raw AST -> resolved AST
  -- generates a good error message if `RawAst.WellFormed` does not hold
  -- ensures `Ast.WellFormed`
- `TypeChecker`: operates on a well-formed resolved AST
  -- check if AST is type correct
  -- ensures `TypeCorrect`
- `StaticConsistency`: operates on a well-formed resolved AST
  -- statically enforce additional consistency conditions
- `Verifier`: resolved AST -> calls to `RSolver.{Extend,Prove}`
- `Semantics`: gives co-inductive big-step semantics for raw AST (note, this file is being rewritten to incorporate new features and to apply to the resolved AST)
