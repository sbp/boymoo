# Power laws for products

`library` is the Library described in `prover/sig/library.md`. Terms and
Steps use the forms in `prover/sig/proof.md`. A result of the form
`(cons value library)` includes the Library with auxiliary lemmas in
insertion order. The entire result is a failure if proof construction or
matching fails. The two goal constructors do not produce a failure.

| Call | Result |
|---|---|
| `(h3-book-power-products-nonzero-product-data library left right left-nonzero right-nonzero)` | Two Steps in a list, proving the product numeric and nonzero, respectively. `left` and `right` prove the factors numeric and the last two Steps prove them nonzero. |
| `(h3-book-power-products-distribute-goal a b n)` | Equality distributing exponent term `n` over the product of base terms `a` and `b`. |
| `(h3-book-power-products-distribution-at-one library target evidence)` | Step proving the distribution equality `target` when its powers all take the value one under the ordered list of Steps `evidence`. |
| `(h3-book-power-products-compose-goal base first second)` | Equality composing two powers of term `base` as a power with exponent `first * second`. Both exponents are terms. |
| `(h3-book-power-products-zero-product-exponent library base first second zero position)` | Step proving that `base` to exponent `first * second` is one. The base and exponents are terms. `zero` proves that the factor at the one-based position is zero. |

`*h3-book-power-products-distribute*` and `*h3-book-power-products-compose*`
are the unprefixed names used to add and cite the two induction lemmas.

Call `(h3-book-power-products-power-products-theorem-with-library library formula)`
when handling a failure and continuing with the Library. It returns
`(cons value library)`, with a Step, `nil`, or a failure in `value`.
The Library includes any auxiliary lemmas added before that result.

In `zero-product-exponent`, positions 1 and 2 select the factors in order.
Negative positions count from the end of the application. `t` selects the
first factor. `nil` selects position zero, the operator. An absent position
indicated by `:none` produces a failure.
