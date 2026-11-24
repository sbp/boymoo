# Scaling

Terms, symbols and Steps use the forms in `prover/sig/proof.md`. A Library
has the form in `prover/sig/library.md`. A result written `(cons value lib)`
carries the Library after any auxiliary lemmas have been added. Each
function can instead return a failure as its entire result.

| Call | Result |
|---|---|
| `(b1-scaling-distribute-left-sum lib a b factor)` | A Step distributing the sum of terms `a` and `b` over right factor `factor`. |
| `(b1-scaling-integer-multiple lib)` | `(cons name lib)` for the positive integer multiple lemma. |
| `(b1-scaling-positive-multiple lib integral pos-scalar pos-factor)` | `(cons step lib)` proving the product positive from Steps for the positive integer scalar and the positive factor. |
| `(b1-scaling-opposite-sign lib positive-p)` | A Step proving the opposite of the number shown positive by `positive-p` fails the positivity test. |
| `(b1-scaling-negative-from-signs lib numeric not-positive not-zero)` | A Step proving a number's opposite positive, given Steps for numeric type, failure of the positivity test, and inequality to zero. |
| `(b1-scaling-positive-rational-multiple lib rational pos-scalar pos-factor)` | `(cons step lib)` proving the product positive from Steps for the positive rational scalar and the positive factor. |
| `(b1-scaling-scale-test-proof lib rational-scalar positive-factor)` | `(cons step lib)` equating the positivity tests before and after scaling, given the scalar's rational Step and the factor's positivity Step. |
| `(b1-scaling-positive-scale-test lib rational-scalar positive-factor)` | `(cons step lib)` applying the positivity test lemma to the given rational and positivity Steps. |
