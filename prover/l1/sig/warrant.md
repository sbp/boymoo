# Warrant constraints

A WarrantProof is a Proof with kind `:l1-warrant`, stored and read with the Proof accessors in `prover/sig/proof.md`. It stores facts and definitions in insertion-ordered association lists. `l1-warrant-warrant-proof-init` constructs it with the ground theory. Comparison and ChoiceRule records use the constructors and accessors in `prover/l1/sig/witness.md`. Certificates use the operations in `prover/l1/sig/primitive.md`.

Arguments named `proof` are Proof values. A term and a Step have the forms given in `prover/sig/proof.md`. `test` is the badge conditional. Pass `:none` for an absent `guard`. A failed recognition returns `nil`. `choices` is a list of ChoiceRule records in admission order. Pass `t` for `complete` to request a complete certificate. Entry text is an ASCII string including its newlines.

| ACL2 call | Result | Failure |
|---|---|---|
| `(l1-warrant-warrant-proof-init)` | WarrantProof with the ground facts, definitions and primitives. | None. |
| `(l1-warrant-warrant-proof-constant proof term)` | An equality Step for a constant computation, or `nil`. | A failure from reading the term or constructing the Step. |
| `(l1-warrant-warrant-proof-trivial-function-tame proof)` | The simplification Step for the quoted trivial function's tameness, or `nil`. | A failure from simplifying. |
| `(l1-warrant-warrant-proof-simplify proof term evidence definitions)` | A simplification Step, or `nil`. Evidence is a list of Steps and definitions is a list of names. Pass `nil` for omitted lists. | A failure from simplifying, including `Fuel`. |
| `(l1-warrant-warrant-tests comparison)` | `(test guard)` for the counterexample of a Comparison or ChoiceRule, or `nil`. | A failure from reading the terms. |
| `(l1-warrant-warrant-parts data)` | `(comparison test guard)` for the parsed fields of a constraint, or `nil`. | A failure from reading the constraint or its tests. |
| `(l1-warrant-fixed-failure proof comparison test guard)` | `(argument step)` for a fixed failure under badge mismatch. The comparison can be a Comparison or ChoiceRule. | A failure from reading the terms or constructing the Step. |
| `(l1-warrant-implication proof antecedent consequent)` | A Step for the implication of term `antecedent` and the first literal of Step `consequent`. | A failure from constructing the Step. |
| `(l1-warrant-application-selection proof comparison test guard selector bad-argument bad-failure left right)` | `(selected step)` for the selected witness term and its Step. `selector` is a ChoiceRule, `bad-argument` is a term, and `bad-failure` is a Step. Use `*l1-warrant-left-function*` and `*l1-warrant-right-function*` for omitted `left` and `right`. | A failure from reading the terms or constructing the Step. |
| `(l1-warrant-lemma name step)` | `(count source)` for the named lemma. | A failure from writing the entry. |
| `(l1-warrant-direct-selection proof comparison applied selection selected complete)` | `(count source reason)` or `nil`. `applied` and `selected` are terms and `selection` is a Step. | A failure from constructing or writing the certificate. |
| `(l1-warrant-warrant-cases proof parts choices complete)` | `(count source reason)` for the recognized `parts`. | A failure from constructing or writing the certificate. |
| `(l1-warrant-warrant-logic certificates)` | Certificates with the three logic lemmas added in order. | A failure from constructing or adding a lemma. |
| `(l1-warrant-warrant-lemmas proof data choices complete)` | `(count source reason)` for the parsed constraint fields, or `nil` if unrecognized. An empty reason indicates a completed certificate. | A failure from reading the constraint or constructing or writing the certificate. |

`l1-warrant-direct-selection-with-proof`, `l1-warrant-warrant-cases-with-proof`, and `l1-warrant-warrant-lemmas-with-proof` take the same arguments as the corresponding calls above. Each returns `(cons result proof)` with the facts as they stand after temporary lemmas are removed. A failure is the entire result. The calls above return the value component alone.

`*l1-warrant-apply-user-function*` is the `APPLY$-USERFN` symbol datum. `*l1-warrant-application-selector*` is the name of the application-equivalence choice rule.

These Proof operations dispatch on the Proof kind. Each may return a failure from proof construction.

| ACL2 call | Result |
|---|---|
| `(l1-warrant-simplify proof term evidence definitions)` | A simplification Step or `nil`. |
| `(l1-warrant-simplify-first proof step evidence definitions)` | The Step after simplification of its first literal. |
| `(l1-warrant-prove proof term evidence definitions)` | A Step proving the term, or `Unproved` when warrant simplification finds no proof. |

The operations named `l1-warrant-warrant-proof-constant`, `l1-warrant-warrant-proof-trivial-function-tame`, and `l1-warrant-warrant-proof-simplify` take a WarrantProof. A term position is a list of zero-based indices from the outermost term inward. The empty position selects the entire term.

| ACL2 call | Result | Failure |
|---|---|---|
| `(l1-warrant-term-at-place term place)` | The nested member of `term`. | A failure from indexing the term. |
| `(l1-warrant-step-at-place step place)` | The nested member of the first literal of `step`. | A failure from getting the first literal or indexing it. |
| `(l1-warrant-counts-total counts)` | The sum of the list of entry proof step counts. | None. |
| `(l1-warrant-entries-count entries)` | The sum of the counts of the `(name count source)` records. | None. |
| `(l1-warrant-entries-sources entries)` | The byte strings of those records in record order. | None. |

`(l1-warrant-join-sources n sources)` joins a list of source strings in
the given order. Pass `1000000` as the initial fuel `n`. It returns a
`Fuel` failure on exhaustion.
