# Floor intervals and signed remainder bounds

`lib` is a Library. Terms and Steps use the forms in `prover/sig/proof.md`. An argument named for a condition or type is the Step proving it. A pair with a Library has the proof result in its car and the updated Library in its cdr. Each function can return a failure in place of its result.

The constants are `*b2-floor-intervals-floor*`, `*b2-floor-intervals-mod*`, `*b2-floor-intervals-floor-bound*`, `*b2-floor-intervals-mod-elim*`, `*b2-floor-intervals-rem-elim*`, `*b2-floor-intervals-mod-bound*` and `*b2-floor-intervals-floor-theorems*`. The last constant lists the floor theorem symbols for membership tests.

| ACL2 call | Result |
|---|---|
| `(b2-floor-intervals-cases lib test prove)` | Step combining the two case Steps. `prove` is the list of the callback results on the true and false assumptions in that order. |
| `(b2-floor-intervals-floor-interval lib i j rational-i rational-j)` | `(cons (list lower upper) lib)`. The bounds compare floor and its successor to the rational ratio. |
| `(b2-floor-intervals-integer-remainder lib i j typed-i typed-j divisor-positive floor-integer)` | `(cons (list integer-value nonnegative strict) lib)`. The Steps prove integrality, nonnegativity and the strict upper bound on the remainder. |
| `(b2-floor-intervals-restored-dividend lib i j ri rj sign)` | Equality Step restoring the dividend after scaling the ratio. `ri` and `rj` show rationality and `sign` compares the divisor with zero. |
| `(b2-floor-intervals-scaled-dividend lib i j ri rj nonzero)` | Equality Step restoring the dividend using rationality of `i` and `j` and nonzero `j`. |
| `(b2-floor-intervals-modulus-upper lib i j ri rj sign floor-type negative)` | `(cons step lib)` for the comparison between the modulus and its divisor. `negative` is a Boolean. |
| `(b2-floor-intervals-modulus-theorem lib formula prove-floor-type)` | The result of proving the modulus bounds, or a request for a floor type. Pass `nil` to start with no replies. |
| `(b2-floor-intervals-modulus-theorem-resume request floor-type)` | Continue a floor type request with its reply. Return the next request, `(cons step lib)`, or a failure. |
| `(b2-floor-intervals-force-facts lib premise)` | Insertion-ordered alist from literals to Steps for the opened `FORCE` facts. |
| `(b2-floor-intervals-floor-theorem lib name formula)` | `(cons step lib)` for the named floor or remainder theorem. |

`b2-floor-intervals-floor-type-request-p` recognizes a floor type request. The accessors `b2-floor-intervals-floor-type-library`, `b2-floor-intervals-floor-type-i` and `b2-floor-intervals-floor-type-j` take the request and return the Library and the two terms for the callback. The reply is `(cons step lib)` with the Library after the callback, or a failure. The optional reply list `prove-floor-type` supplies replies in request order. Each reply uses the Library at the corresponding request.
