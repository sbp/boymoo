# Arithmetic

`*b2-arithmetic-zp*` and `*b2-arithmetic-factorial*` are prover symbols.
The library has the form in `prover/sig/library.md`. Formulas, terms, and
Steps have the forms in `prover/sig/proof.md`. These functions can return
a failure during proof construction.

| Function | Arguments and result |
|---|---|
| `(b2-arithmetic-factorial-positive lib formula)` | Library and the positive-integer factorial formula. Returns its induction Step. |
| `(b2-arithmetic-factorial-properties lib name formula)` | Library, theorem symbol, and factorial formula. Returns the Step for the named property. |
| `(b2-arithmetic-factorial-positive-base halted lib formula term)` | Step for the stopping test, Library, formula, and factorial term. Returns the base Step. |
| `(b2-arithmetic-factorial-positive-advance running hypothesis lib formula n term child)` | Steps for the advancing test and induction hypothesis, Library, formula, induction variable, factorial term, and next argument. Returns the recursive case Step. |

`(b2-arithmetic-require key table)` returns the value of the prover
datum `key` in the insertion-ordered association list `table`, or a failure
if the key is absent.
