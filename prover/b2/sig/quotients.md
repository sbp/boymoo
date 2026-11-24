# Quotient bounds

Terms, Steps, and Libraries have the forms specified in
`prover/sig/proof.md` and `prover/sig/library.md`. The Library supplies
B2 tactics. Arguments named `types` and `evidence` are ordered lists of
Steps. Each function can return a failure in place of its result. When a
function can add a lemma, its result carries the Library even if all the
lemmas it needs are already there.

The term constants are `*b2-quotients-niq*`, `*b2-quotients-nfix*`,
`*b2-quotients-ifix*`, `*b2-quotients-zp*`, and `*b2-quotients-floor*`.

| ACL2 call | Arguments and result |
|---|---|
| `(b2-quotients-product-negation lib a b types)` | Terms `a` and `b`. Returns `(cons step lib)` for the product-negation equality. |
| `(b2-quotients-product-difference lib scale a b types)` | Terms `scale`, `a`, and `b`. Returns `(cons step lib)` for distribution of the scaled difference `b - a`. |
| `(b2-quotients-scaled lib comparison scale scale-positive types strict)` | An input comparison Step, a scale term, a Step proving its positivity, type evidence, and a Boolean for strict comparison. Returns `(cons step lib)` for the scaled comparison. |
| `(b2-quotients-natural-proof lib term typed nonnegative)` | A term, an integer Step, and a nonnegative Step. Returns a naturality Step. |
| `(b2-quotients-nonnegative-quotient lib upper)` | Boolean `upper` selects the interval lemma when true and the bound lemma when false. Returns `(cons label lib)` with the corresponding lemma name term and Library. |
| `(b2-quotients-cross-product lib i j d n represented divisor-inverse integer-i)` | Four terms followed by the representation equality, divisor inverse, and integer evidence Steps. Returns a cross-multiplication equality Step. |
| `(b2-quotients-floor-bounds lib i j int-i int-j pos-i pos-j greater-j)` | Dividend and divisor terms with integer and positive Steps for each, plus a Step proving that the divisor is greater than one. Returns `(cons (list natural decrease product-bound) lib)`. |
| `(b2-quotients-floor-descent lib i j int-i int-j pos-i pos-j greater-j)` | The same arguments and result shape as `b2-quotients-floor-bounds`, citing the instantiated floor lemma. |
| `(b2-quotients-ilog-decrease lib goal evidence)` | An ordinal comparison goal term and its evidence Steps. Returns `(cons step lib)` with a proof of the comparison and the resulting Library. |
