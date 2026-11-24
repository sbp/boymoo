# Multiplication of bases and exponents

`lib` is a Library as specified in `prover/sig/library.md`, and a Step has the form in `prover/sig/proof.md`. The tables give arguments in ACL2 order. All calls can return a failure from proof construction in place of their listed result. A method that adds a lemma returns the Library with that lemma appended.

| ACL2 call | Arguments and result |
|---|---|
| `(t2-power-products-inverse-product-equation lib left right per-factor)` | `left` and `right` are terms. `per-factor` contains Steps proving the individual inverse products equal to one, in left-to-right order. Returns a Step proving the grouped inverse product equals one. |
| `(t2-power-products-both-one lib product first second)` | `product` is a product term and `first` and `second` are equality Steps for its factors. Returns a Step equating the product to one. |
| `(t2-power-products-distribute-nonzero lib)` | Step for distribution of exponentiation over multiplication of nonzero numeric bases, with the original hypotheses. |
| `(t2-power-products-base-product lib)` | Library with `SELF-POWER-BASE-PRODUCT`. |
| `(t2-power-products-base-reciprocal lib)` | Library with `SELF-POWER-BASE-RECIPROCAL`. |
| `(t2-power-products-negate-exponent lib)` | Library with `SELF-POWER-NEGATE-EXPONENT`. |
| `(t2-power-products-scaled-exponent lib exponent previous scale integers forward)` | The three operands are terms, `integers` contains integer evidence Steps, and `forward` selects the positive increment when true. Returns a Step equating the scaled exponent to the sum built from the increment and the scaled previous exponent. |
| `(t2-power-products-combine-exponents-nonzero lib)` | Step for multiplying the exponents of a nested power of a nonzero numeric base, with the original hypotheses. |
| `(t2-power-products-combine-exponents lib)` | Library with `SELF-POWER-EXPONENT-PRODUCT`. |
| `(t2-power-products-scaled-recurrence-expanded exponent integral lib iz)` | `exponent` is a term and `integral` and `iz` are evidence Steps for the integrality of `exponent` and `Z`, respectively. Returns the step for the reordered exponent product. |
| `(t2-power-products-scaled-recurrence lib)` | Library with `SELF-POWER-SCALED-RECURRENCE`. |
| `(t2-power-products-order-translation lib)` | Library with `SELF-FIELD-ORDER-TRANSLATION`. |
| `(t2-power-products-strict-then-weak lib lower upper types)` | `lower` is a Step for `bottom < top` and `upper` a Step for `top <= middle`. `types` is the list of order evidence Steps in argument order. Returns a Step for `bottom < middle`. A mismatched endpoint returns a failure. |
| `(t2-power-products-power-gap lib)` | Library with `SELF-POWER-GAP-LOWER-BOUND`. |
| `(t2-power-products-build lib)` | Library with the seven lemmas above in the order of the build. |

The Step-producing calls `distribute-nonzero`, `combine-exponents-nonzero`
and `strict-then-weak` return `(cons step lib)` on success. The Library
includes any countdown and order lemmas added during the deduction. A
failure is the entire result.
