# Arithmetic normalization

`proof` is the H1 Prover from `tactics`. Terms and Steps have the forms
given in `prover/sig/proof.md`. Tests are ordered pairs `(term holds)`, with
`t` for true and `nil` for false. Evidence Steps are used in list order.

The symbols `*h1-book-arithmetic-fix*`, `*h1-book-arithmetic-reciprocal*`,
`*h1-book-arithmetic-iff*`, and `*h1-book-arithmetic-expt*` stand for
`FIX`, `UNARY-/`, `IFF`, and `EXPT`. The association list
`*h1-book-arithmetic-operators*` maps `PLUS` to `"+"` and `TIMES` to
`"*"`, in that order.

| Call | Result | Failure |
|---|---|---|
| `(h1-book-arithmetic-rational-constant term)` | ACL2 rational for a quotation of an integer or tagged ratio. Returns `nil` for other terms. | A failure from indexing the quotation or forming the ratio. |
| `(h1-book-arithmetic-compute-rational proof term)` | Constant-computation Step for a recognized call on quoted rationals, or `nil`. | A failure from reading the term or constructing the Step. |
| `(h1-book-arithmetic-right-unit proof operator term)` | Step reducing the sum with zero on the right or the product with one on the right. `operator` is the prover symbol for `PLUS` or `TIMES`. | A proof failure, or a failure for an unknown operator. |
| `(h1-book-arithmetic-collapse-fix proof term numeric)` | Step reducing `(FIX term)` with the supplied numeric or nonnumeric evidence Step. | A proof failure. |
| `(h1-book-arithmetic-sum-with-fix proof)` | Step showing that fixing the first summand preserves the sum. | A proof failure. |
| `(h1-book-arithmetic-same-equality-value proof left right forward reverse)` | Step equating the Boolean values of the terms `left` and `right`. The Steps `forward` and `reverse` prove each from the other. | A proof failure. |
| `(h1-book-arithmetic-cancel-addend proof formula)` | Step for equality after cancellation of a common addend, or `nil` when the formula has another form. | A failure from reading the formula or constructing the proof. |
| `(h1-book-arithmetic-minus-as-product proof)` | Step expressing unary negation as multiplication by negative one. | A proof failure. |
| `(h1-book-arithmetic-install-arithmetic proof)` | The Prover with the arithmetic rules and helper lemmas installed in order. | A proof or rule-registration failure. |
| `(h1-book-arithmetic-at term place)` | Subterm at the list of successive zero-based indices `place`. | A failure from indexing. |
| `(h1-book-arithmetic-algebraic-proof proof formula)` | Step proving `formula` by arithmetic normalization and restoring its premises. | `Unproved` when normalization does not close the goal, or a proof failure. |

## Algebra

An Algebra has the form `(:h1-algebra proof context work)`. Its `context`
is the H1 Context from `tactics` and retains the insertion order of evidence
and bindings. Its `work` starts at 150 and is decremented at each call of
`normal`, including calls that exhaust the limit. Use the constructor and
accessors below.

| Call | Result | Failure |
|---|---|---|
| `(h1-book-arithmetic-algebra-init proof tests evidence)` | New Algebra with context initialized from `tests` and the supplied `evidence` inserted and bound in order. Pass `nil` for omitted evidence. | A failure from context construction or evidence insertion. |
| `(h1-book-arithmetic-algebra-proof self)` | The Algebra's Prover. | — |
| `(h1-book-arithmetic-algebra-context self)` | The Algebra's Context. | — |
| `(h1-book-arithmetic-algebra-work self)` | The Algebra's remaining integer work budget. | — |
| `(h1-book-arithmetic-algebra-with-context self context)` | The Algebra with its Context replaced. | — |
| `(h1-book-arithmetic-algebra-with-work self work)` | The Algebra with its integer work budget replaced. | — |
| `(h1-book-arithmetic-algebra-assoc self head x y z)` | Associativity Step for the binary operator symbol `head` and terms `x`, `y`, `z`. | A failure for an unknown operator or from proof construction. |
| `(h1-book-arithmetic-algebra-commute self head x y)` | Commutativity Step for the binary operator symbol `head` and terms `x`, `y`. | A failure for an unknown operator or from proof construction. |
| `(h1-book-arithmetic-algebra-normal self term)` | `(cons step self)` with the normalization Step and the resulting Algebra. | `Unproved` when the work budget is exhausted, or a proof failure. |
| `(h1-book-arithmetic-algebra-distribute self term)` | Distributivity Step, or `nil` when neither factor is a sum. | A failure from reading the term or constructing the proof. |
| `(h1-book-arithmetic-algebra-associate self step head)` | Step right-associating the operator `head` in the right side of the equality Step. | A proof failure or `Fuel`. |
| `(h1-book-arithmetic-algebra-sort self step head)` | Step sorting the right-associated spine of `head` in the equality Step's right side. | A proof failure or `Fuel`. |
| `(h1-book-arithmetic-algebra-sort-key term self head)` | Triple of the nonconstant flag, written base, and written term, in comparison order. | A failure from reading or writing a term. |
| `(h1-book-arithmetic-algebra-coefficient self term)` | Two-element list of the coefficient and the base. | A failure from reading a term. |
| `(h1-book-arithmetic-algebra-collect self left right)` | `(cons step-or-nil self)` with a sum-collection Step when applicable, and the resulting Algebra. | A proof failure. |
| `(h1-book-arithmetic-algebra-collect-with-coefficient term value self base numeric)` | Step making coefficient `value` explicit on `term`. `base` is the base term and `numeric` its numeric evidence Step, when needed. | A proof failure. |
| `(h1-book-arithmetic-algebra-cancel-reciprocal self left right)` | `(cons step-or-nil self)` with a reciprocal-cancellation Step when applicable, and the resulting Algebra. | A proof failure. |
| `(h1-book-arithmetic-algebra-combine self step head)` | `(cons step self)` with the Step combining adjacent operands and the resulting Algebra. | A proof failure or `Fuel`. |
| `(h1-book-arithmetic-algebra-equality self left right)` | `(cons step self)` with the Step equating `left` and `right` and the resulting Algebra. | `Unproved` when the normal forms differ, or a proof failure. |
| `(h1-book-arithmetic-algebra-order self goal)` | `(cons step self)` with the order proof for `goal` and the resulting Algebra. | `Unproved` when no bound is found, or a proof failure. |

For these Algebra calls that return a pair, a failure occupies the value
position. A caller that makes another attempt can use the resulting
Algebra. `associate` and `sort` return the transformed Step.

`(h1-book-arithmetic-algebra-with-proof self proof)`
replaces the Prover used by the Algebra and its Context's Search, keeping
the Context evidence, bindings, and current work budgets.
