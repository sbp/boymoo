# Countdown

The constants `*t2-countdown-lognot*`, `*t2-countdown-cl-abs*`, and
`*t2-countdown-minusp*` are the Common Lisp symbols for `LOGNOT`, `ABS`,
and `MINUSP`. The Library is an Arithmetic object as described in
`prover/t2/sig/arithmetic.md`. A term and Step use the forms in
`prover/sig/proof.md`. An ordinal decrease goal contains the comparison
symbol, child measure, and parent measure. Every call can return a failure in
place of the complete result.

| Call | Result |
|---|---|
| `(t2-countdown-absolute-count lib integral)` | `(cons step lib)` for equality of Common Lisp absolute value and ACL2 count, from the integer Step. |
| `(t2-countdown-fixed-absolute-ordinal lib measure)` | `(cons step lib)` for ordinality of the fixed absolute measure term. |
| `(t2-countdown-fixed-absolute-count lib measure hypotheses)` | `(list step lib hypotheses)` for eliminating `IFIX` in the absolute measure using the hypothesis context. |
| `(t2-countdown-signed-premise lib value hypotheses negative)` | `(list step lib hypotheses)` for the signed bound on the value term, strict negativity when `negative` is true and strict positivity when it is nil. |
| `(t2-countdown-nonpositive-count-lemma lib)` | The Library with the count for a nonpositive integer. |
| `(t2-countdown-magnitude-predecessor lib negative int-value)` | The naturalness Step for one less than the magnitude, using the negative bound Step and the integer Step. |
| `(t2-countdown-negative-countdown lib goal hypotheses)` | `(list step lib hypotheses)` for integer countdown descent. |

For RulerFacts, `t2-countdown-fixed-absolute-count-query`,
`t2-countdown-signed-premise-query`, and `t2-countdown-negative-countdown-query`
take the same arguments followed by the list of replies, using the request
protocol and accessors in `prover/t2/sig/arithmetic.md`. The ordinary entry
points take the underlying shared Hypotheses object.

The ordinary entry points also accept the RulerFacts context described in
`prover/t2/sig/guarded-selectors.md`.

A bare Hypotheses object supports find and require. When a recipe requests
premises, as `fixed-absolute-count` does, the ordinary entry point requires
RulerFacts and returns a failure on bare Hypotheses.
