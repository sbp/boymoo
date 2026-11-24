# Finite choice

Proofs, Steps, and terms have the forms in `prover/sig/proof.md`.
The tests are a list of `(test key)` pairs in argument traversal order.
False tests are an alist from test terms to Steps in insertion order.

| Function | Arguments in order | Result | Failure |
| --- | --- | --- | --- |
| `l1-finite-choice-variable-free-in` | Variable term, term | Boolean indicating a free occurrence | Malformed term |
| `l1-finite-choice-equality-tests` | Term, argument variable | All pairs `(test key)` found by the equality-test search | `NonEqualityArgument` for an unsupported occurrence, or a failure from traversing the term |
| `l1-finite-choice-differing-value` | Proof, value term | `(bit step)` with a Boolean term and the Step proving it differs from the value | Proof construction |
| `l1-finite-choice-fresh-argument` | Proof, argument variable, test list, key list | `(default false-tests)` with a default term and the corresponding alist of equality Steps | Missing test key or proof construction |
| `l1-finite-choice-default-equation` | Proof, failure term, argument variable, default term, false-tests alist | Equality Step for the original and default failures when the tests are false | Proof failure |
| `l1-finite-choice-finite-choice-selected-failure` | Representative index, equality Step, Proof, accepted Step list, rejected Step list, representative failure list, failure term, argument variable | Step for selection under the representative's failure | Proof failure |
| `l1-finite-choice-finite-choice` | Proof, argument variable, failure term | `(selected step)` with the representative selection term and the Step proving necessity, or `nil` if the test search rejects the failure | Proof or traversal failure |

Every key list produced by finite choice contains keys in first occurrence
order. Repeated assignments to a false-tests key retain its position.
