# Convenience features

This section describes additional convenience features of the B3 language.

(sec-autoinv)=
## Auto-invariants

....TODO: see concept document

A variable can be introduced with an _auto-invariant_, declared by the optional `autoinv` clause.
The expression in an `autoinv` clause must have type `bool` and can mention any variable in scope,
including the variable being introduced. An auto-invariant 
....TODO: show example use
