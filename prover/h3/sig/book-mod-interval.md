# Remainder interval proofs

`lib` is a Library, and terms and Steps use the forms in `prover/sig/proof.md`.
`context` is a Bounds object described in `prover/h3/sig/book-order.md`.
`signs` is a Signs value described in `prover/h3/sig/book-signs.md`.
An evidence list is in argument order. Evidence read from Bounds is in
insertion order.

Each proof call can return a failure in place of its result. A result of the
form `(cons value lib)` holds the returned value and the Library with any
auxiliary lemmas, in the order they were added. A missing optional Step is
`nil` in the value position of the pair.

| ACL2 call | Arguments and result |
|---|---|
| `(h3-book-mod-interval-finite-product lib amount rational-divisor)` | Endpoint term and rationality Step for its multiplier. Returns the product reduction Step, or `unproved` for an unsupported endpoint. |
| `(h3-book-mod-interval-mixed-remainder lib call rational nonrational numeric-dividend)` | Remainder term and Steps for one argument's rationality, the other argument's nonrationality, and the dividend's numeric type. Returns the Step equating the remainder to the dividend. |
| `(h3-book-mod-interval-sum-of-remainders lib left right divisor)` | Rationality Steps for the summands and divisor. Returns the Step using the named sum congruence, or `unproved` when the congruence is absent. |
| `(h3-book-mod-interval-replace-remainder lib step equality)` | Step to rewrite and equality Step to apply. Returns the rewritten Step. |

`(h3-book-mod-interval-remainder-interval-theorem-with-library lib name formula)`
has the same arguments. It returns `(cons result lib)` on success and on a
failure. Use this form when a tactic catches `unproved` and continues with the
auxiliary lemmas added before that failure.
