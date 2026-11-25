# Floor translation

A Library, Step, and term have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. A `known` table maps literals to Steps and retains
first-insertion order. A `solver` is the Types object specified
by `prover/b2/sig/numeric-types.md`. It uses the Library supplied as `lib`.
A result of `(cons step solver)` carries the resulting solver and its
Library, including any auxiliary lemmas. A result of `(cons step library)`
carries the resulting Library directly. A failure is the entire result.

| ACL2 call | Arguments and result | Failure |
|---|---|---|
| `(b2-floor-translation-rational-type lib term known solver)` | Library, target term, evidence table, and Types object. Returns `(cons step solver)` proving the target rational. | Failure from selecting the rational operation or from proof construction, or `fuel` on exhaustion. |
| `(b2-floor-translation-unique-integer lib ratio first second ratio-type first-type second-type first-bounds second-bounds)` | Library, ratio and two candidate terms, three Steps proving their respective types, and two lists of Steps giving the bounds in lower-to-upper order. Returns `(cons step library)` proving the two candidates equal. | Failure from proof construction. |
| `(b2-floor-translation-ratio a b)` | Numerator and divisor terms. Returns the term for the numerator times the divisor's reciprocal. | — |
| `(b2-floor-translation-remainder-as-product lib a d known solver remainder)` | Library, dividend and divisor terms, evidence table, Types object, and remainder operation symbol. Pass `*b2-floor-intervals-mod*` for the default. Returns `(cons step solver)` proving the product representation of the remainder. | Failure from evidence lookup or proof construction. |
| `(b2-floor-translation-floor-translation-theorem lib name formula)` | Library, theorem name symbol, and formula term. Returns `(cons step library)` proving the formula. | Failure from evidence lookup or proof construction. |

The symbol `*b2-floor-translation-rem*` is the `COMMON-LISP` symbol `REM`.
`*b2-floor-translation-translations*` lists the theorem names used to
select a floor translation recipe.
