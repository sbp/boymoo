# Remainder descent and bounds

`proof` is the H2 search proof object used by the book prover. Its library contains the facts, definitions and entries described in `prover/sig/library.md`. Terms and Steps are as in `prover/sig/proof.md`. A call that changes the proof returns `(cons value proof)` with the updated object. This includes changes to the search configuration by `derive`. Every function can return a failure in place of its result.

`*h2-modular-mod*`, `*h2-modular-natural-fix*` and `*h2-modular-zp*` are the ACL2 symbol terms `NONNEG-INT-MOD`, `NFIX` and `ZP` respectively.

| ACL2 call | Result |
|---|---|
| `(h2-modular-fixed-natural proof)` | Pair of the lemma name string for natural closure of `NFIX` and the proof. |
| `(h2-modular-natural-value proof natural)` | Step stating that `NFIX` leaves the natural number in Step `natural` unchanged. |
| `(h2-modular-remainder-step proof)` | Pair of the lemma name string for remainder subtraction descent and the proof. |
| `(h2-modular-remainder-bounds proof)` | Pair of the lemma name string for the remainder bounds and the proof. |
| `(h2-modular-remainder-count-bound proof)` | Pair of the lemma name string for the strict count bound on the remainder and the proof. |
| `(h2-modular-remainder-theorem proof formula)` | Pair of the Step for the remainder comparison term `formula` and the proof. |
| `(h2-modular-quotient-guard proof test dividend divisor typed positive)` | Pair of an equality Step aligning the test term with the remainder test and the proof. `typed` and `positive` are Steps for the divisor. |
| `(h2-modular-quotient-remainder proof formula)` | Pair of the Step for the quotient and remainder identity term `formula` and the proof. |
| `(h2-modular-small-remainder proof formula)` | Pair of the Step for the zero dividend or unit divisor equation term `formula` and the proof. |
| `(h2-modular-quotient-identity proof n d)` | The quotient and remainder identity fact instantiated at terms `n` and `d`. |
| `(h2-modular-remainder-zero-product proof zero)` | The quotient and remainder identity Step simplified by Step `zero`, which equates the remainder to zero. |
| `(h2-modular-division-of-exact-multiple proof label formula)` | Pair of the Step for the divisibility term `formula` selected by the string `label` and the proof. |
| `(h2-modular-remainder-is-zero proof relation divisor-type delta-type divisor-positive lower upper)` | Step equating the remainder to zero. The inputs after `proof` are Steps giving the product relation, integrality of each factor, positivity of the divisor, and the lower and upper bounds. |
| `(h2-modular-exact-multiple-has-zero-remainder proof formula)` | Pair of the Step for the exact multiple term `formula` and the proof. |
| `(h2-modular-positive-gcd proof formula)` | Pair of the Step for the greatest common divisor positivity term `formula` and the proof. |

The two quotient and remainder helpers take the enclosing proof values after their other arguments.

| ACL2 call | Result |
|---|---|
| `(h2-modular-quotient-remainder-base remainder-eq quotient-eq proof total zero-product drop-zero)` | Step for the base case using the two opening equality Steps, the proof, the sum term `total`, and the Steps for the zero product and zero addend. |
| `(h2-modular-quotient-remainder-fixed-value value fact evidence proof)` | Step for the fix of term `value` from the fact name string and the premise Step `evidence`. |

The proof argument is the inherited Recipes object specified in `prover/h2/sig/recipes.md`. It holds the Search and name map used by searches. The pure product and book-logic operations take its Search, and operations that add library entries use its Library.

`h2-modular-library` and `h2-modular-proof` take a Recipes object and return its Library and the Library's Proof, respectively. `h2-modular-first-at` takes a Step and a list of zero-based term indices and follows the indices from the Step's first literal. `h2-modular-tail-of-size` takes a term and a size and unpacks the term's slice from index 1 with that size. `h2-modular-bindings` takes an ordered list of binding pairs and an initial binding alist and installs the bindings in the supplied order. `h2-modular-derive` takes a Recipes object, formula, definition string, fact name list, seed Step list and case term list and returns the result of `derive` with the other options at their defaults. `h2-modular-introduce` takes a Recipes object, implication and conclusion Step and returns its implication Step.

`h2-modular-term-at` follows a list of zero-based indices from a term. `h2-modular-with-search-results` is the ordered binding abbreviation from `prover/sig/proof2.md` with propagation of Search hook requests as well. A modular entry point that invokes a search can return a Search request as its entire result under the replay protocol in `prover/h2/sig/search.md`.

`fixed-natural`, `natural-value`, `remainder-step`, `remainder-bounds` and `remainder-count-bound` also accept the inherited Search directly. In those calls, a returned proof has the same form as the input proof.
