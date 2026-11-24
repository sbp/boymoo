# Evaluator equations

`lib` is a Library as specified in `prover/sig/library.md`. Terms and Steps
have the forms in `prover/sig/proof.md`. A declaration is `(function arity)`
and a named formula is `(name formula)`. Each declaration, named formula,
and primitive in an argument list retains its source position. Evidence
arguments in this book are lists of Steps. Pass `nil` for omitted evidence
or changes. A proof entry has the form returned by `proof-proof-entry`.

An EvaluatorNames object is `(:t3-evaluator-names prefix core value values)`.
Use `(t3-book-evaluators-evaluator-names-init name)` to construct it from
the original evaluator symbol. The constructor can return a failure from
writing the symbol. The four field accessors are
`t3-book-evaluators-evaluator-names-prefix`,
`t3-book-evaluators-evaluator-names-core`,
`t3-book-evaluators-evaluator-names-value`, and
`t3-book-evaluators-evaluator-names-values`. Each takes the record and returns the corresponding field. `prefix` is a string and the remaining fields are symbols.

| Call | Result | Failure |
|---|---|---|
| `(t3-book-evaluators-evaluator-names-rule names label)` | The prefix from `names` followed by the string `label`. | None. |
| `(t3-book-evaluators-second value)` | The term `CAR` of `CDR` of `value`. | None. |
| `(t3-book-evaluators-third value)` | The term `CAR` after two applications of `CDR` to `value`. | None. |
| `(t3-book-evaluators-argument-selectors values arity)` | The first `arity` selectors of the argument-list term `values`, in argument order. | A failure for an invalid range bound. |
| `(t3-book-evaluators-define-evaluator lib names primitives)` | The Library with the core evaluator, aliases and alias equations appended. `primitives` is a list of `(function arity)` pairs. | A failure from proof construction or term traversal. |
| `(t3-book-evaluators-expanded lib names call evidence changes)` | The evaluation equation for `call` with the equality Steps in `changes` applied in order and the result simplified using `evidence`. | A failure from proof construction. |
| `(t3-book-evaluators-view lib function equation)` | The equality for `function` applied to the two sides of the equality Step `equation`, with the right side simplified. | A failure from proof construction. |
| `(t3-book-evaluators-on-atom lib selector value atom)` | The completion equation for `selector` applied to term `value` under the negative `CONSP` Step `atom`. | A failure from proof construction. |
| `(t3-book-evaluators-evaluator-selectors lib names)` | The Library with the first and rest lemmas appended in that order. | A failure from proof construction. |
| `(t3-book-evaluators-list-case lib value evidence)` | The unfolded and simplified `TRUE-LISTP` equation for `value`. | A failure from proof construction. |
| `(t3-book-evaluators-tail-induction lib formula present)` | The pair `(bindings step)` for the tail induction hypothesis of `formula`, under the positive `CONSP` Step `present`. | A failure from proof construction. |
| `(t3-book-evaluators-quoted-values lib names)` | The Library with the proper-values and quoted-values lemmas appended in that order. | A failure from proof construction. |
| `(t3-book-evaluators-symbol-is-atom lib typed)` | A negative `CONSP` Step for the term in the positive `SYMBOLP` Step `typed`. | A failure from proof construction. |
| `(t3-book-evaluators-quote-excluded lib value signed)` | A Step excluding the quoted `QUOTE` symbol for `value`, given the input Step `signed`. | A failure from proof construction. |
| `(t3-book-evaluators-equation-constraint lib names formula index)` | A Step proving the evaluator constraint `formula` at the zero-based `index`. | `Unsupported` for an incompatible branch, or a construction failure. |
| `(t3-book-evaluators-evaluator-shape declarations formulas)` | The Boolean recognition of the first eight evaluator equations. | A failure from reading a malformed formula or declaration. |
| `(t3-book-evaluators-witness lib declarations formulas)` | `(cons entry lib)` with the witness proof entry and the Library extended with the evaluator definitions and lemmas. | A failure from reading the constraints or constructing the proof. |

The constants are `*t3-book-evaluators-eval*`,
`*t3-book-evaluators-flag-eval*`, `*t3-book-evaluators-mode*`,
`*t3-book-evaluators-assoc*`, `*t3-book-evaluators-pairlis*`,
`*t3-book-evaluators-kwote*`, `*t3-book-evaluators-kwote-list*`,
`*t3-book-evaluators-mv-nth*`, and `*t3-book-evaluators-symbolp*`.
Failures are the entire result. A caller handling a witness failure can
continue from its input Library.

`(t3-book-evaluators-witness-goals formulas functions)` returns the
ordered list of formula terms after replacement from the association list
`functions`. It can return a failure from the replacement or a malformed
named formula.

The arity can be an integer, `nil` for zero, or `t` for one.
The absent bound `:none` gives a generic failure.
