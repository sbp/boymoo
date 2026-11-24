# Rational order

`lib` is the B2 tactic library. Terms and Steps have the forms in
`prover/sig/proof.md`. Every call can return a failure in place of its result.

| ACL2 call | Arguments and result |
|---|---|
| `(b2-rational-order-reverse-negations lib a b)` | Terms `a` and `b`. Returns the equality Step relating the comparison of their negations to the reversed comparison. |
| `(b2-rational-order-difference-orders lib a b typed-a typed-b)` | Terms `a` and `b` followed by their rational Steps. Returns `(list delta typed opened reverse)` with the difference term, its rational Step and the two comparison equality Steps. |
| `(b2-rational-order-weak-from-strict lib comparison typed-a typed-b)` | The strict comparison Step and rational Steps for its left and right terms. Returns the corresponding weak comparison Step. |
| `(b2-rational-order-strict-from-weak lib weak unequal typed-a typed-b)` | The weak comparison and distinctness Steps, then rational Steps for its lower and upper terms. Returns the strict comparison Step. |
| `(b2-rational-order-rational-lexorder lib a b typed-a typed-b)` | Two terms and their rational Steps. Returns the equality Step relating lexicographic and weak rational order. |
| `(b2-rational-order-weak-order-chain lib a b c typed-a typed-b typed-c first second)` | Three terms, their rational Steps and the two adjacent weak comparison Steps. Returns their weak composition Step. |
| `(b2-rational-order-rational-order-chain lib first second types)` | Adjacent comparison Steps and a three-element list of rational Steps for their endpoints in chain order. Returns their composition Step. |
| `(b2-rational-order-sign-cases lib value typed distinct prove)` | A term, its rational Step, its distinctness-from-zero Step, and the ordered callback replies described below. Returns `(cons step lib)` after joining the branches. |

`sign-cases` visits the negative branch before the positive branch. Pass
`nil` for `prove` to request its first callback arguments. Each reply is a
pair `(cons step lib)` with the callback's Step and resulting library. If
the next reply is missing, the result is
`(cons (list :call negative sign facts) lib)`, where `negative`, `sign`,
and `facts` are the callback arguments. Invoke the callback
with those arguments and the returned library, append its reply to
`prove`, and repeat from the original arguments. The callback can return
a failure in the Step position. `facts` is a list in the supplied evidence order.
