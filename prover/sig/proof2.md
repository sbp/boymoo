# Derived proof rules

`prover/proof2.lisp` makes, from the eight rules of `prover/proof.lisp`, the rules that the tactics work with: equalities, conditionals, cases, simplification and a small prover. Terms, the Proof and the Step have the forms of `prover/sig/proof.md`.

In every call `proof` is a Proof. `step`, `equality`, `evidence`, `first`, `yes`, `no` and `test-proof` are Steps; an equality is a Step whose first literal is `(EQUAL left right)`. Where a list of evidence or of definitions is asked for, `nil` is the empty list. A rule works on the first literal of a Step and carries its side literals, and those of its premises, into the Step it returns. No function changes its arguments. Every function can return a failure in place of its value (`prover/FAILURES.md`), its own or one from the rules it uses; the tables name the kinds that a function adds.

## Reading terms

| Call | Value | Failure |
|---|---|---|
| `(proof-term-at term index)` | The member of the list `term` at `index`, from 0. | `"type"` for an integer. `"index"` when the list is too short. |
| `(proof-list-of-length term size)` | The list `term` when it has `size` members. | `"type"` for an integer. `"value"` for another length. |
| `(proof-datum-head datum)` | The first member of a datum that is a list, and `nil` for any other. | None. |
| `(proof-rewritten-term equality)` | The right side of the first literal of an equality. | Those of the two above. |
| `(proof-quoted-values terms)` | The list of the data of a list of constants. | Those of `proof-term-at`. |
| `(proof-datum-text datum)` | `(proof-datum-text datum)`, the text of a datum in the message of a failure. | None. |
| `(proof-list-index-error)` | The failure `(:failure "index" "")`. | |

`(proof-with-checked-results ((name form) ...) result)` is a macro. It binds each name in order to the value of its form, and returns the first value that is a failure. When none is, it returns the value of `result`.

## Equalities

| Call | Value | Failure |
|---|---|---|
| `(proof-proof-unfold proof term)` | The equality of the call `term` and the body of its function with the arguments in the place of the formals. | `"key"` when the function has no definition. `"assertion"` when the numbers of arguments and formals differ. |
| `(proof-proof-reflexive proof term)` | The equality of `term` and itself. | |
| `(proof-proof-symmetric proof equality)` | From `(EQUAL a b)`, the equality `(EQUAL b a)`. | |
| `(proof-proof-chain proof first rest)` | From `first`, `(EQUAL a b)`, and the equalities of the list `rest` in order, `(EQUAL b c)` and so on, the equality of `a` and the last right side, tidied. A `nil` in `rest` is passed over. | |
| `(proof-proof-transport proof step equality)` | From a Step of `right` and the equality `(EQUAL left right)`, a Step of `left`. | |
| `(proof-proof-true-from-eq proof equality)` | From `(EQUAL term 'T)`, a Step of `term`. | `"assertion"` when the right side is not `'T`. |

## Truth and conditionals

| Call | Value | Failure |
|---|---|---|
| `(proof-proof-nil-or-true proof term)` | A Step of the clause `((EQUAL term 'NIL) term)`. | |
| `(proof-proof-not-nil proof)` | A Step of `(NOT 'NIL)`. | |
| `(proof-proof-excluded-middle proof term)` | A Step of the clause `((NOT term) term)`. | |
| `(proof-proof-assume proof term holds)` | A Step of the same two literals: `term` first when `holds` is `t`, and `(NOT term)` first when it is `nil`. The first literal is what is assumed, and the side literal records the assumption until a cut removes it. | |
| `(proof-proof-discharge proof step evidence)` | `(proof-discharge proof step evidence)` of `prover/sig/proof.md`: the Step without one side literal, which the evidence settles. | `"value"` when no side literal fits. |
| `(proof-proof-if-false proof term)` | For `term` of the form `(IF a b c)`, a Step of `(EQUAL term c)` with the side literal `a`. | `"value"` when `term` does not have four members. |
| `(proof-proof-if-true proof term)` | For the same form, a Step of `(EQUAL term b)` with the side literal `(NOT a)`. | The same. |
| `(proof-proof-select proof term evidence)` | For the same form and evidence whose first literal is `a` or `(NOT a)`, the equality of `term` and the branch that the evidence chooses, discharged with the evidence. | `"assertion"` when the evidence is of neither literal. |
| `(proof-proof-prove-if proof step test-proof)` | From a Step of `(IF a b c)` and a Step of `a` or of `(NOT a)`, a Step of the branch chosen. | |
| `(proof-proof-conjunct proof step)` | From a Step of `(IF a b 'NIL)`, the list of a Step of `a` and a Step of `b`. | `"assertion"` when the last branch is not `'NIL`. |
| `(proof-proof-modus-ponens proof step evidence)` | From a Step of `(IMPLIES p q)` and a Step of `p`, a Step of `q`. | `"assertion"` when the first literal is not such a call. `"assertion"` or `"value"` when the evidence is not a Step of `p`. |
| `(proof-proof-cases proof test yes no)` | From `yes`, a Step of a claim that may have the side literal `(NOT test)`, and `no`, a Step of the same claim that may have the side literal `test`, a Step of the claim without the two. When `yes` does not have its side literal the value is `yes`, and otherwise when `no` does not have its own the value is `no`. | `"assertion"` when the first literals of `yes` and `no` differ. |

## Proof by the cases of a value

A term `value` is taken apart by its conditionals: at `(IF a b c)` the branch `b` is read under the test `(a t)` and the branch `c` under `(a nil)`, a lambda application is replaced by its body with the actuals in it, and any other term is a leaf. `tests` is the list of the tests `(term holds)` that hold where `value` stands, `nil` at the top.

| Call | Value | Failure |
|---|---|---|
| `(proof-proof-by-value-leaves proof value tests)` | The list of the leaves, each `(leaf tests)` with the tests that lead to it, the branch of a true test before that of a false one. | `"Fuel"`. |
| `(proof-proof-by-value proof value template leaf tests)` | A Step of `template` with `value` in the place of the slot `*proof-result*`. `leaf` is a table whose keys are the leaves `(leaf tests)` and whose values are Steps, each of `template` with its leaf in the slot. A value that is a failure is returned when its leaf is reached. | `"value"` when a leaf has no entry. `"assertion"` when a Step's first literal is not `template` with the leaf in the slot. `"Fuel"`. |
| `(proof-by-value-join proof value template yes no)` | For `value` of the form `(IF a b c)`, the Step of `template` with `value` in the slot, from the Steps `yes` and `no` of `template` with `b` and with `c` in the slot. | |

A caller gets the leaves from `proof-proof-by-value-leaves`, proves each, and gives the Steps to `proof-proof-by-value` in a table in that order.

## Simplification and the prover

| Call | Value | Failure |
|---|---|---|
| `(proof-proof-constant proof term)` | An equality of `term` and a simpler term when `term` is a computation that the kind of the Proof knows (below), and `nil` otherwise. | |
| `(proof-proof-simplify proof term evidence definitions)` | An equality of `term` and its simplified form, or `nil` when nothing in it can be simplified. `evidence` is a list of Steps and `definitions` a list of the symbols of functions that may be unfolded. | `"Fuel"`. |
| `(proof-proof-simplify-first proof step evidence definitions)` | The Step with its first literal simplified, tidied, or `step` itself when nothing can be simplified. | `"Fuel"`. |
| `(proof-proof-prove proof term evidence definitions)` | A Step of `term`. | `"value"`, with the message `No proof of` and the text of the term, when simplification leaves a term that is not `'T` and cannot be simplified. `"Fuel"`. |

`proof-proof-simplify` reads a term from the outside. A variable or a constant stays. A lambda application, or a call of a function in `definitions`, is replaced by its body and the body is simplified. In `(IF a b c)` the test is simplified; when the test is then `'NIL` or `'T`, or a Step of `evidence` has the test or its negation as its first literal, the branch chosen takes the place of the conditional and is simplified, and otherwise the branches are left as they are. In any other call the arguments are simplified in order and then `proof-proof-constant` is asked about the result.

`proof-proof-prove` returns a proof of `'T` at once, and the Step of `evidence` whose first literal is `term` when there is one. Otherwise it simplifies `term`: when the result is `'T` the proof is done, and when it is another term that term is proved in the same way and the proof is carried back.

## What the kind of a Proof chooses

The kind of a Proof (`prover/sig/proof.md`) chooses the form of `proof-proof-reflexive`, `proof-proof-constant` and `proof-proof-by-value`, in every rule that uses them.

| Rule | `:base` | `:slice` | `:book` |
|---|---|---|---|
| `proof-proof-reflexive` | From the fact `"equal-same"`. | The fact `SELF-EQUALITY-REFLEXIVE` when the Proof has it. | As `:slice`. |
| `proof-proof-constant` | `(EQUAL a a)` for any term `a`. On constants: `EQUAL`, `CONSP`, `INTEGERP`, `RATIONALP`, `STRINGP`, `COMPLEX-RATIONALP`, and on integers `<`, `BINARY-+`, `BINARY-*` and `UNARY--`. | Also `ACL2-NUMBERP`, `CHARACTERP` and `SYMBOLP` of a constant. | Also `CAR`, `CDR` and `CONS` of constants, `CODE-CHAR` and `CHAR-CODE` of a constant, and `COERCE` of constants. |
| `proof-proof-by-value` | By the two branches of each conditional and `proof-proof-cases`. | The same, but for the template `(ACL2-NUMBERP *proof-result*)` when the Proof has the fact `SELF-NUMBER-IF`: that fact joins two branches that do not depend on the test. | As `:slice`. |

`(proof-proof-reflexive-base proof term)` and `(proof-proof-constant-base proof term)` are the `:base` forms, whatever the kind. `(proof-uses-slice-rules-p proof)` is whether the kind is `:slice` or `:book`. `proof-proof-assume`, `proof-proof-if-false` and `proof-proof-if-true` use the facts `SELF-EXCLUDED-MIDDLE`, `SELF-IF-FALSE` and `SELF-IF-TRUE` when the Proof has them, whatever its kind.

## Parts that other books call

| Call | Value |
|---|---|
| `(proof-find-evidence evidence literals)` | The first Step of the list `evidence` whose first literal is in the list `literals`, or `nil`. |
| `(proof-simplify-expansion proof term)` | For a lambda application or a call of a defined function, the list of the equality of `term` and its body, and that body. |
| `(proof-simplify-if-redex term first)` | The conditional `term` with the right side of the equality `first` as its test, or `term` itself when `first` is `nil`. |
| `(proof-simplify-if-select proof redex evidence)` | For a conditional `redex`, the equality of it and a branch when its test is `'NIL` or `'T` or the evidence settles the test, and `nil` otherwise. |
| `(proof-simplify-if-path proof term first evidence)` | One move of the simplifier at the conditional `term`, `first` being the equality of its simplified test or `nil`: `(:simplify equality branch)` when a branch was chosen and is to be simplified next, and otherwise the equality reached so far, or `nil`. |
| `(proof-simplify-argument-result proof term index result equality)` | The equality `result` of `term`, or the reflexive one when `result` is `nil`, with the equality of the argument at `index` applied on its right side. `result` itself when `equality` is `nil`. |
| `(proof-prove-step proof term evidence definitions)` | One move of `proof-proof-prove`: a Step of `term`, a failure, or `(:transport simplified equality)` when the simplified term is to be proved next. |
| `(proof-prove-unproved-term term)` | The failure of `proof-proof-prove`. |
| `(proof-constant-call-parts term)` | `term` itself when it is a list that is not empty. Failure `"type"` for an integer and `"value"` for the empty list. |
| `(proof-constant-book-argument args index)` | The member of the list at `index`, or the failure `"index"`. |
| `(proof-constant-book-list proof term)` | The `proof-proof-compute` Step of a call of `CAR`, `CDR` or `CONS` on constants. |
| `(proof-constant-cons-value head tail)` | The datum of the cons of the data `head` and `tail`: the list of `head` when `tail` is the symbol `*proof-nil*`, the list `tail` with `head` before it when `tail` is a list, and otherwise `(head ("dot" tail))`. |
| `(proof-constant-character-data chars)` | The list of the data `("char" code)` of a list of characters. |
| `(proof-constant-coerced-value value kind)` | The datum of `(COERCE value kind)`: for the symbol `COMMON-LISP::LIST`, the list of the characters of a string datum, or `*proof-nil*`; for any other `kind`, the string datum of the characters of a list. |
