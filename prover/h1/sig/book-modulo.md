# Remainders and quotients

`proof` is an H1 proof world. Terms and Steps have the forms in `prover/sig/proof.md`. `tests` is a list of `(term holds)` pairs in input order, where `holds` is `t` or `nil`. A failure replaces the entire result.

`*h1-book-modulo-fix*`, `*h1-book-modulo-ifix*`, `*h1-book-modulo-mod*` and `*h1-book-modulo-quotient*` are the symbol data for `NFIX`, `IFIX`, `NONNEG-INT-MOD` and `NONNEGATIVE-INTEGER-QUOTIENT` in the ACL2 package.

| Call | Result | Failure |
|---|---|---|
| `(h1-book-modulo-fixed-natural proof term natural)` | List of the integrality and nonnegativity Steps, given a natural-number Step for `term`. | From a proof operation. |
| `(h1-book-modulo-natural-from-positive proof integral sign)` | Natural-number Step for the term proved integer by `integral` and positive by `sign`. | From a proof operation. |
| `(h1-book-modulo-fix-value proof term natural)` | Step selecting the value of `(NFIX term)` under `natural`, a positive or negative natural-number Step. | From a proof operation. |
| `(h1-book-modulo-ifix-value proof term integral)` | Step selecting the value of `(IFIX term)` under `integral`, a positive or negative integer Step. | From a proof operation. |
| `(h1-book-modulo-positive-divisor proof term not-zp)` | Positive-integer Step for `term` given a Step `not-zp` proving `(not (ZP term))`. | From a proof operation. |
| `(h1-book-modulo-subtraction-conditions before amount)` | The two signed tests for subtracting term `amount` from term `before`, first the false `ZP` test and then the false strict bound test. | — |
| `(h1-book-modulo-subtraction-facts proof before amount not-zp enough)` | List of Steps for the natural parent, natural difference, positive amount and lower bound on the parent, given the Steps for the two signed tests. | From a proof operation. |
| `(h1-book-modulo-subtraction-decreases proof before amount not-zp enough)` | Decrease Step for `NFIX` after the subtraction under the same two test Steps. | From a proof operation. |
| `(h1-book-modulo-install-subtraction proof)` | Proof world with the subtraction lemmas in order. | From a proof operation. |
| `(h1-book-modulo-subtraction-amount before after tests)` | The subtracted term when `after` and `tests` describe the guarded subtraction from `before`. `:none` denotes an unmatched subtraction. | A failure on a short call in a matched shape. |
| `(h1-book-modulo-bounded-remainder before after tests)` | Whether `after` is a remainder call with divisor `before` and `tests` contains its false `ZP` test. | A failure on a short remainder call. |
| `(h1-book-modulo-bounded-decrease proof before after tests)` | Decrease Step for a guarded subtraction or remainder, or `nil` if neither matches. | From testing the shape or constructing the Step. |
| `(h1-book-modulo-ifix-inside proof dividend divisor bound sign typed-divisor)` | Step comparing the fixed dividend with `divisor`, given the bound on its `NFIX` value and the positive and integer Steps for `divisor`. | From a proof operation. |
| `(h1-book-modulo-open-quotient proof dividend divisor divisor-fixed divisor-type ifix-bound)` | Step selecting a quotient branch, given the divisor's `NFIX` equation, its positive-integer Step and the bound test on the `IFIX` dividend. | From a proof operation. |
| `(h1-book-modulo-quotient-at-zero-divisor proof dividend divisor divisor-is-zero)` | Step for the quotient when the divisor's `NFIX` value is zero. | From a proof operation. |
| `(h1-book-modulo-remainder-spec remainder)` | List of the four terms for natural remainder, natural quotient, remainder bound and quotient identity, given a remainder application. | A failure for a malformed application. |
| `(h1-book-modulo-prove-remainder proof)` | Step for the remainder and quotient invariant. | From a proof operation. |
| `(h1-book-modulo-install-small-remainders proof)` | Proof world with the small-remainder lemmas in order. | From a proof operation. |
| `(h1-book-modulo-install-remainder proof)` | Proof world with the remainder and quotient lemmas in order. | From a proof operation. |

The following operations are shared by book installers. Each returns a failure if a proof operation fails.

| Call | Result |
|---|---|
| `(h1-book-modulo-first-at step place)` | The subterm of the first literal at the indices in `place`, read left to right. |
| `(h1-book-modulo-lemma proof name step conditions)` | Proof world with `step` registered under the unprefixed `name` and the given condition terms. |
| `(h1-book-modulo-record-formula proof label step)` | `(cons fact-step proof)` with the fact and the updated proof world. `label` is the unprefixed name, and the formula is registered with `rewrite` false. |
