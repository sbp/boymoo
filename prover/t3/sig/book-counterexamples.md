# Occurrence counts and permutation counterexamples

`lib` is a Library with the T3 proof rules for its dispatch tag. Terms and Steps
have the forms in `prover/sig/proof.md`. The constants are
`*t3-book-counterexamples-count*`, `*t3-book-counterexamples-find*`,
`*t3-book-counterexamples-fix*` and `*t3-book-counterexamples-checked-count*`.

A Multiplicities object has the form `(:t3-multiplicities lib natural)`,
where `natural` is the Step proving that the occurrence count is natural.
Use the constructor and accessors below. Inputs are unchanged by these
functions.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t3-book-counterexamples-occurrence-comparison x y)` | Equality term comparing the occurrence counts of a counterexample in the given terms `x` and `y`. | None. |
| `(t3-book-counterexamples-statement x y)` | Permutation counterexample formula on the two terms. | None. |
| `(t3-book-counterexamples-list-statement x y)` | The same formula under the true-list hypotheses. | None. |
| `(t3-book-counterexamples-equal-successors lib a b integers)` | Step equating equality of the successors of terms `a` and `b` with equality of `a` and `b`. `integers` is the ordered list of integer evidence Steps. | A failure from proof construction. |
| `(t3-book-counterexamples-multiplicities-init lib)` | A Multiplicities object with the natural occurrence count Step built in `lib`. | A failure from proof construction. |
| `(t3-book-counterexamples-multiplicities-lib counts)` | The Library field of Multiplicities object `counts`. | None. |
| `(t3-book-counterexamples-multiplicities-natural counts)` | The natural occurrence count Step of `counts`. | None. |
| `(t3-book-counterexamples-multiplicities-natural-at counts term)` | Natural occurrence count Step specialized at count term `term`. | A failure from proof construction or a malformed count term. |
| `(t3-book-counterexamples-multiplicities-integer-at counts term)` | Integer occurrence count Step specialized at count term `term`. | A failure from proof construction or a malformed count term. |
| `(t3-book-counterexamples-multiplicities-zero-inequality counts comparison)` | Step proving that equality term `comparison`, which compares a successor count with zero, is false. | A failure from proof construction or a malformed comparison. |
| `(t3-book-counterexamples-counterexample lib name formula)` | The theorem entry at symbol `name` for true lists, using the given formula term. | A failure from proof construction or serialization. |
| `(t3-book-counterexamples-perm-fixed lib fixed-x fixed-y)` | Step equating permutation of the given fixed terms with permutation of X and Y. | A failure from proof construction. |
| `(t3-book-counterexamples-convert lib name formula)` | The theorem entry at symbol `name` for arbitrary lists. The proof uses the fixed true-list theorem. | A failure from proof construction or serialization. |
