# Floor

`lib` is a B1 Library. Terms, symbols, and Steps have the forms in
`prover/sig/proof.md`. An interval is a three-element list of Steps, in order,
for the integral floor, the weak lower bound, and the strict upper bound.
`sums` is the NumberSums object in `prover/b1/sig/arithmetic.md` and `numbers`
is a list of evidence Steps in the order supplied. Every function can return a failure
in place of the whole result. When a result includes an updated Library, it
is `(cons value lib)`.

| ACL2 call | Result |
|---|---|
| `(b1-floor-quotient-interval lib rational representation int-n int-d pos-d nonnegative)` | An interval for the rational quotient paired with the updated Library. The arguments after `lib` are Steps for rationality, the quotient representation, integrality of the numerator and denominator, positivity of the denominator, and nonnegativity of the numerator. |
| `(b1-floor-floor-interval-lemma lib)` | The name of the self-floor interval fact, paired with the Library containing it. |
| `(b1-floor-floor-of-ratio lib floor)` | An equality Step expressing the `floor` term as the floor of its quotient by one. |
| `(b1-floor-interval lib floor rational)` | An interval for the `floor` term and its rationality Step `rational`, paired with the updated Library. |
| `(b1-floor-strict-then-weak lib sums strict weak numbers)` | A strict comparison Step formed by composing Steps `strict` and `weak`. |
| `(b1-floor-weak-then-strict lib sums weak strict numbers)` | A strict comparison Step formed by composing Steps `weak` and `strict`. |
| `(b1-floor-advance-bound lib strict int-a int-b)` | A weak bound Step from strict integer comparison Step `strict` and integrality Steps `int-a` and `int-b`, paired with the updated Library. |
| `(b1-floor-unique-interval-lemma lib)` | The name of the interval uniqueness fact, paired with the Library containing it. |
| `(b1-floor-equal-intervals lib first second rational)` | An equality Step for the floors of intervals `first` and `second` with rationality Step `rational`, paired with the updated Library. |
| `(b1-floor-quotient-of-mod lib mod divisor i-value integral-i rational-xy rational-xz)` | A three-element list containing the quotient equality, integral offset, and rationality Steps, paired with the updated Library. `mod` and `divisor` are terms. The remaining arguments are the equality and integrality Steps for the multiplier and the rationality Steps for the two quotients. |
| `(b1-floor-translate-floor lib original shifted rational-original rational-shifted ratio integer-offset)` | A Step relating floor terms `original` and `shifted`, paired with the updated Library. The remaining arguments are Steps for rationality of their quotients, the relation between the quotients, and the integrality of the offset. |
| `(b1-floor-rewrite-floor-mod lib formula)` | A Step for the displayed floor of a remainder formula, paired with the updated Library. |
| `(b1-floor-fixed-product lib left right numeric-left)` | A Step equating the product of terms `left` and `right` to the product with its right operand fixed. `numeric-left` is evidence that `left` is numeric. |
| `(b1-floor-rewrite-mod-mod lib formula)` | A Step for the displayed remainder of a remainder formula, paired with the updated Library. |
