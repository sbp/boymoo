# Equalities of integer powers

A Library, term and Step have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. The constant `*t2-exponent-equalities-abs*` is the
prover symbol for `COMMON-LISP::ABS`.

All calls can return a failure. A call that returns only a Library
is the resulting Library with any added lemmas.
A call that returns a Step and a Library uses `(cons step lib)`.

| ACL2 call | Arguments and result |
|---|---|
| `(t2-exponent-equalities-absolute-power lib)` | Library with `POWER-ABSOLUTE` added. |
| `(t2-exponent-equalities-equality-from-exponents lib base left right)` | Given three terms, a Step equating powers of `base` under equality of their exponents `left` and `right`. |
| `(t2-exponent-equalities-positive-injectivity-incompatible strict lib integers ratio wide pos narrow left)` | Given a strict exponent comparison Step, integer evidence Steps in exponent order, base rationality Step, greater-than-one term, positivity Step, less-than-one Step and power equality term, a Step denying equality of the powers. |
| `(t2-exponent-equalities-positive-injectivity lib)` | Library with `POWER-POSITIVE-INJECTIVE` added. |
| `(t2-exponent-equalities-nonexceptional lib)` | Three Steps assuming that the base `X` differs from −1, 0 and 1, in that order. |
| `(t2-exponent-equalities-magnitude-domain lib is-rational distinct-bases)` | From a rationality Step for `X` and the three Steps from `nonexceptional`, returns the rationality, positivity and difference-from-one Steps for its absolute value, in that order. |
| `(t2-exponent-equalities-absolute-comparison lib known absolute-left absolute-right)` | From an equality Step and the absolute-value equations for its two sides, a Step equating the absolute values after those equations are applied. |
| `(t2-exponent-equalities-signed-injectivity lib)` | Library with `POWER-EQUAL-EXPONENTS` added. |
| `(t2-exponent-equalities-unit-on-other-bases lib iy ratio)` | Given an integer Step for `Y` and a rationality Step for `X`, returns the two comparison Steps of the power to 1 and −1, in that order. |
| `(t2-exponent-equalities-compare-value lib equation unit)` | Given the equation Step for a power and a unit term, a Step equating the comparison of the power with the unit to its computed Boolean. |
| `(t2-exponent-equalities-compare-minus-one-powers lib iy unit)` | Given an integer Step for `Y` and a unit term, returns a Step expressing the unit comparison for a power of −1, paired with the Library. |
| `(t2-exponent-equalities-exact-units lib)` | Library with `POWER-EQUAL-ONE` and `POWER-EQUAL-MINUS-ONE` added in that order, with any auxiliary lemma added at its first use. |
| `(t2-exponent-equalities-translated-order lib strict amount)` | Given a strict comparison Step and a term, the Step for translating the comparison by the term. |
| `(t2-exponent-equalities-consecutive-powers-of-two-weaker lower upper bound lib base ratio integers wide)` | Given lower and upper exponent terms, weak bound Step, base term, rationality Step, integer evidence Steps and greater-than-one Step, a Step for the weak comparison of the powers. |
| `(t2-exponent-equalities-consecutive-powers-of-two-contradiction strict incompatible position lib equality)` | Given strict and incompatible weak comparison Steps, an argument index and the power equality term, a Step denying the equality. |
| `(t2-exponent-equalities-consecutive-powers-of-two lib)` | Library with `POWERS-OF-TWO-DIFFER-BY-ONE` added. |
| `(t2-exponent-equalities-build lib)` | Library extended by the absolute, positive injectivity, signed injectivity, exact unit and consecutive-power recipes in that order. |
