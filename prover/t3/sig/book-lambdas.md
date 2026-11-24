# Lambda recognizer proofs

`lib` is a Library as specified in `prover/sig/library.md`. Terms and Steps
have the forms in `prover/sig/proof.md`. `facts` is an association list of
`(first-literal . step)` entries in insertion order. `evidence` is a list of
Steps. Pass `nil` for omitted evidence. In a theorem entry point `name`
is a theorem symbol and `formula` is its statement term. A proof entry
has the form returned by `proof-proof-entry`. Every function can return
a failure as its entire result.

| Call | Result |
|---|---|
| `(t3-book-lambdas-inspect lib call evidence)` | The equation for the unfolded recognizer `call`, simplified using `evidence`. |
| `(t3-book-lambdas-required lib formula facts)` | A Step establishing `formula` from `facts`, or `Unsupported` for a missing condition. |
| `(t3-book-lambdas-not-symbol lib cons)` | A negative `SYMBOLP` Step from the positive `CONSP` Step `cons`. |
| `(t3-book-lambdas-present-operator lib operator facts)` | A positive `CONSP` Step for `operator` from its length condition in `facts`. |
| `(t3-book-lambdas-extract-lambda lib name formula)` | The theorem entry extracting a pseudo-lambda recognizer from a pseudo-term recognizer. |
| `(t3-book-lambdas-pseudo-lambda-from-term lib typed present excludes-quote nonsymbol target)` | A Step for `target` derived from Steps for the term recognizer, cons test, exclusion of quote, and symbol denial, respectively. |
| `(t3-book-lambdas-open-application lib target)` | The recognizer equation for `target` after simplifying the two selectors of its application argument. |
| `(t3-book-lambdas-construct-lambda lib name formula)` | The theorem entry for a pseudo-term constructed from a pseudo-lambda. |
| `(t3-book-lambdas-normalize-checks lib value evidence)` | A Step equating `value` to the normalized recognizer conjunction, or `nil` if unchanged. |
| `(t3-book-lambdas-conditions lib proof)` | The Steps from recursively opening the conjunction in `proof`, visiting left before right. |
| `(t3-book-lambdas-proper-length lib)` | The Library with the proper-list length lemma appended. |
| `(t3-book-lambdas-term-list-proper lib proof)` | A proper-list Step from a Step for the real term-list recognizer. |
| `(t3-book-lambdas-arglist-proper lib typed)` | A proper-list Step from an `ARGLISTP` Step, or `Unsupported` when the recognizer does not supply the proof. |
| `(t3-book-lambdas-extract-real-lambda lib name formula)` | `(cons entry lib)` with the real lambda extraction theorem entry and the Library with the length lemma. |
| `(t3-book-lambdas-construct-real-lambda lib name formula)` | `(cons entry lib)` with the real lambda construction theorem entry and the Library with the length lemma. |
| `(t3-book-lambdas-application-with-lambda lib typed arguments arity target)` | A Step for `target` from the lambda recognizer, argument-list recognizer and arity Steps. |
| `(t3-book-lambdas-returned-boolean lib call earlier)` | A Step proving the Boolean closure of `call`. `earlier` is an alist from function symbols to lemma name strings. Induction substitutions follow the order of the first visit to each recursive child. |
| `(t3-book-lambdas-lambda-boolean lib name formula)` | `(cons entry lib)` with the Boolean theorem entry and the Library with the two Boolean closure lemmas. |

The symbol constants are `*t3-book-lambdas-pseudo-lambda*`,
`*t3-book-lambdas-logic-fns*`, `*t3-book-lambdas-logic-list*`,
`*t3-book-lambdas-real-term*`, `*t3-book-lambdas-real-list*`,
`*t3-book-lambdas-arglist*`, `*t3-book-lambdas-w*`,
`*t3-book-lambdas-construct*`, `*t3-book-lambdas-symbolp*`,
`*t3-book-lambdas-stringp*`, `*t3-book-lambdas-length*`,
`*t3-book-lambdas-extract-real*`, `*t3-book-lambdas-construct-real*`, and
`*t3-book-lambdas-booleanp*`. `*t3-book-lambdas-definitions*` is the ordered
list of recognizer definitions used while reducing a call.
`*t3-book-lambdas-proper-length*` is the string name of the length lemma.

`(t3-book-lambdas-returned-boolean-leaf value tests lib call earlier measure
original substitutions)` proves the Boolean result at one leaf. `value`
is the returned term under the signed `tests`. The closure supplies the
original `call`, earlier lemma names, count `measure`, original Boolean
goal, and a map from recursive children to their binding pairs. The result
is `(cons step substitutions)` with the updated map, or a failure.
