# Slice proof library

`SliceLibrary` extends the base proof theory and uses the Library representation
and constructor in `prover/sig/library.md`. `lib` is that Library object.
Terms and Steps have the forms in `prover/sig/proof.md`. Each call can return
a failure in place of its listed result. A result written `(cons value lib)`
contains the value and the Library after any additions to it.

| Function | Arguments in order | Result |
|---|---|---|
| `lemmas-positive-nonzero-integer` | `lib`, `value` (term), `integrality`, `nonzero`, `bound` (Steps) | `(cons step lib)` proving that `value` is positive |
| `lemmas-nfix-equation` | `lib`, `value` (term) | `(cons step lib)` proving equality of the two clipping functions at `value` |
| `lemmas-slice-library-share-proofs` | `lib`, `obligations` (list of `(clause step)`), `forbidden` (list of terms) | `(cons steps lib)` with one proof per clause in order |
| `lemmas-slice-library-build` | `lib` | Library with the slice definitions and lemmas |
| `lemmas-slice-library-reflexive` | `lib`, `term` | Step proving `term` equals itself |
| `lemmas-slice-library-number` | `lib`, `term`, `evidence` (list of Steps) | `(cons step lib)` proving numeric type |
| `lemmas-slice-library-natural` | `lib`, `term` | `(cons step lib)` proving natural type |
| `lemmas-slice-library-type-of` | `lib`, `term`, `evidence` (list of Steps) | `(cons step lib)` proving integer type |
| `lemmas-slice-library-by-value` | `lib`, `value`, `template` (terms), `leaf` (alist), `tests` (list of test pairs) | Step proving the instantiated template |
| `lemmas-slice-library-count-lemmas` | `lib` | Library with the numeric and count lemmas |

`leaf` in `by-value` uses the format from `prover/sig/proof2.md`. It maps
each `(value tests)` to its Step or failure. `tests` is a list of `(test holds)`
pairs, with `t` for a true test and `nil` for a false test. The arguments
Use `nil` for empty `forbidden`, `evidence`, and `tests` lists.

The term constants are `*lemmas-reflexive*`, `*lemmas-len-number*`,
`*lemmas-number-if*`, `*lemmas-length*`, `*lemmas-nfix*`, `*lemmas-min*`,
`*lemmas-characterp*`, and `*lemmas-symbolp*`.

`lemmas-slice-library-rational` takes `lib`, `term`, and `evidence` and
returns `(cons step lib)` or a failure. It uses the base rational
method using the slice integer method. This form also supplies the
latest library when type reasoning has added an auxiliary lemma.

| Shared function | Arguments in order | Result |
|---|---|---|
| `lemmas-self-name` | `name` (string) | Prover symbol with `SELF-` prepended to the name. |
| `lemmas-has-fact` | `lib`, `name` (fact name) | `t` if the fact exists, or `nil`. |
| `lemmas-slice-library-types` | `lib`, `terms` (list of terms), `evidence` (list of Steps) | `(cons steps lib)` proving integrality in term order, or a failure. |

The Step form in `prover/sig/proof.md` carries the rule, its arguments,
and its clause. The sharing calculation compares that entire form.
