# Guarded application proofs

A Proof, Step and term have the forms in `prover/sig/proof.md`. An
Application reduction object has the form in `prover/l1/sig/application.md`.
A badge is the unquoted badge datum, and badge tests and equations are
terms. A certificate result `(count source)` contains the sum of the
proof step counts and the concatenated lemma text in emission order.

| ACL2 call | Arguments and result | Failure |
|---|---|---|
| `(l1-guarded-tame-arguments proof reduction function badge)` | A Proof, an Application reduction object, a function name, and its badge. Returns `(step subject)`, the unfolded tameness Step and its subject term. | A failure from reduction or proof construction, or a failed assertion. |
| `(l1-guarded-split-arguments proof reduction argument-list)` | A Proof, an Application reduction object, and a Step for the remaining argument list. Returns the head and tail Steps as a two-element list. | A failure from reduction or proof construction, or a failed assertion. |
| `(l1-guarded-quoted-function argument)` | An argument term. Returns the nested tests for a quoted tame function designator. | None. |
| `(l1-guarded-quoted-arguments proof badge-test)` | A Proof and its badge equality term. Returns the certificate result for function-valued positions in ascending position order. | A failure from reading the badge, reduction, proof construction, or writing. |
| `(l1-guarded-badge-validity proof badge-equation)` | A Proof and a badge equation term. Returns the certificate result for badge validity and the bare designator restriction. | A failure from reduction or proof construction, a failed assertion, or a failure from writing. |
| `(l1-guarded-constant-lambdas proof arguments)` | A Proof and the argument list term. Returns the certificate result for tameness and evaluation of a constant lambda. | A failure from reduction or proof construction, a failed assertion, or a failure from writing. |
| `(l1-guarded-result-calls term names)` | A term and a set of names as a list. Returns the calls of those names, retaining repetitions in term traversal order. | A failure from term traversal or substitution. |

`*l1-guarded-take-failure*` is the symbol for the argument normalization
lemma. The audit has no output on success. A failure is the entire result.
