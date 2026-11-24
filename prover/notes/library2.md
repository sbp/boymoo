# The lemmas of order, length and size

The signatures and the table of the lemmas are in `prover/sig/library2.md`.

## The build in three parts

`library-library-build` is `library-library-build-before-count`, `library-library-count-lemmas` and `library-library-build-after-count`. A Library of the kind `:slice` or `:book` is built from the same three with lemmas of its own between them: `lemmas-slice-library-build` of `prover/lemmas.lisp` adds `SELF-EQUALITY-REFLEXIVE`, runs the first part, adds `SELF-NUMBER-IF` and `SELF-LEN-NUMBER`, calls `library-library-count-lemmas-for-slice`, and runs the last part.

The proofs of the count lemmas depend on the kind of the Proof and on those two facts. `ABS-NUMBER`, `LENGTH-NUMBER` and `COUNT-NUMBER` are proved by the cases of the body of each function (`proof-proof-by-value`). With the kind `:slice` or `:book`, two branches that do not depend on their test are joined by `SELF-NUMBER-IF`, a leaf that is a call of `LEN` is settled by `SELF-LEN-NUMBER`, and a leaf that is a constant by `proof-proof-prove`. The clauses of the lemmas are the same for every kind; their step lines need not be.

## The order

Each group cites lemmas of the groups before it, so the order of the build is fixed. The ordered arithmetic uses the rules of sums of `prover/library.lisp`. Among the lemmas cited, the order lemmas cite `LESS-DIFFERENCE`, `POSITIVE-SUM`, `POSITIVE-PLUS-NONNEGATIVE` and `POSITIVE-NONNEGATIVE`; the length lemmas cite `NATURAL-SUM`, `NATURAL-INTEGER` and `SUCCESSOR-LARGER`; the count lemmas cite `NUMBER-FINITE` and `NATURAL-INTEGER`; the weak selectors cite `FINITE-ORDER`, `LESS-TO-WEAK` and `COUNT-NATURAL`; the integer measures cite `POSITIVE-NONNEGATIVE`, `NATURAL-FROM-BOUNDS`, `NFIX-INTEGER` and `FINITE-ORDER`.

`LEN-NATURAL` is the one lemma of the build that is proved by induction, on the measure `(ACL2-COUNT X)` with the smaller instance at `(CDR X)`.

## The rules of comparison

`library-library-compare-chain`, `library-library-as-weak` and `library-library-ordinal-comparison` ask `library-library-type-of` for the integer type of what they compare, with no evidence. They are for the terms whose type the Library knows by itself: sizes, lengths, constants and their sums. A book that compares other terms proves their types first and cites the lemma itself, as `descent-ordinal-comparison` of `prover/descent.lisp` does for `FINITE-ORDER`.

A weak comparison is the literal `(NOT (< b a))`. There is no function `<=` in a clause of the Library.

## The two measures

`SELF-NFIX` and `SELF-GAP` are the Library's own definitions, added by `prover/library.lisp`. `NFIX-DECREASE` and `GAP-DECREASE` are the lemmas by which a measure of that form is shown to decrease: `(SELF-GAP bound i)` for a counter `i` that rises toward `bound`. `prover/descent.lisp` cites `GAP-DECREASE` in its gap recipe.
