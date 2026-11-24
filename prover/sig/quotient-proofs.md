# Quotient proofs

The `lib` argument is a Library. A term and a Step have the forms in
`prover/sig/proof.md`. The `rulers` argument is a Rulers object as described in
`prover/sig/rulers.md`. An argument named `types` is a list of integer Steps.
Arguments for positivity, nonnegativity and ordering are Steps with the
indicated comparison as their first literal.

`*quotient-proofs-floor*`, `*quotient-proofs-truncate*`,
`*quotient-proofs-quotient*`, `*quotient-proofs-numerator*`,
`*quotient-proofs-denominator*` and `*quotient-proofs-reciprocal*` are the
corresponding prover symbols.

Each function that takes a Library can return a failure in place of the
listed result. A result written as `(value . lib)` pairs the value with
the resulting Library. An optional value is `nil` when absent.

| ACL2 call | Arguments and result |
|---|---|
| `(quotient-proofs-count-order lib a b types nonnegative-a nonnegative-b less)` | For terms `a` and `b` with their weak bounds by zero and a proof of `a < b`, returns the Step for count descent paired with the Library. |
| `(quotient-proofs-quotient-hypotheses i j)` | Terms for the dividend and divisor. Returns the conjunction of their natural, integer and positive hypotheses. |
| `(quotient-proofs-quotient-properties i j value)` | Terms for the dividend, divisor and quotient. Returns the conjunction of the quotient's natural and product bounds. |
| `(quotient-proofs-bound-parts lib proof)` | Splits the Step `proof` for the quotient properties into a list of natural, lower and upper Steps. |
| `(quotient-proofs-product-successor lib divisor value types)` | Divisor and integer terms. Returns the Step distributing the divisor over one plus the integer. |
| `(quotient-proofs-quotient-lemma lib)` | Returns the Library with the integer quotient bounds lemma. |
| `(quotient-proofs-quotient-bounds lib i j natural-i integer-j positive-j)` | Dividend and divisor terms with Steps for their hypotheses. Returns `((natural lower upper) . lib)`. |
| `(quotient-proofs-reciprocal-cancel lib value types positive-value)` | Integer term with a proof of positivity. Returns the Step for cancellation against its reciprocal. |
| `(quotient-proofs-quotient-ratio lib n radix types positive-radix)` | Integer terms `n` and `radix` and a Step proving a positive radix. Returns a list of the numerator and denominator terms, their integer Steps, the denominator's positive Step and the cross-product equality Step. |
| `(quotient-proofs-radix-assumptions lib)` | Returns a list of the four assumption Steps as a list and the derived positive-radix Step. |
| `(quotient-proofs-radix-product-lemma lib function)` | Given a floor or truncate symbol, returns the lemma name string paired with the Library. |
| `(quotient-proofs-radix-less-lemma lib function)` | Given a floor or truncate symbol, returns the lemma name string paired with the Library. |
| `(quotient-proofs-radix-lemma lib function)` | Given a floor or truncate symbol, returns the lemma name string paired with the Library. |
| `(quotient-proofs-dividend-rulers lib value base rulers)` | Dividend and radix terms and their Rulers. Returns the optional list `(integer-step positive-step)` paired with the Library. |
| `(quotient-proofs-quotient-call lib term value)` | A proposed quotient `term` and its dividend term. Returns the optional list `(call opening)`, whose second element is an optional equality Step. |
| `(quotient-proofs-quotient-decrease lib goal rulers)` | The proposed count comparison term and its Rulers. Returns an optional proof Step paired with the Library. |
| `(quotient-proofs-radix-calls lib formula)` | A formula term. Returns the candidates `(variable child changes test holds)` in traversal order. Each change is a two-element list `(old new)`. |
| `(quotient-proofs-radix-calls-start formula)` | Returns the initial scan cursor for the formula term. |
| `(quotient-proofs-radix-calls-next lib cursor)` | Returns `(candidate . cursor)` for the next candidate, or `nil` at exhaustion. |
| `(quotient-proofs-prove-radix-induction-base lib candidate)` | Returns the initial branch evidence, a singleton list of Steps. |
| `(quotient-proofs-prove-radix-induction lib formula candidate)` | After the base branch is proved, returns `((induction evidence) . lib)`, where `induction` is the TreeInduction object and `evidence` is the list of Steps for the inductive branch. A missing descent returns `(nil . lib)`. |
| `(quotient-proofs-prove-radix-induction-finish lib candidate induction base step)` | Finishes the induction given the candidate, prepared TreeInduction, and the base and inductive branch Steps. Returns the proof Step. |

The branch proof function belongs to the caller of the induction. For
each candidate, the caller proves the formula with the base evidence,
prepares the induction, proves the formula with the inductive evidence,
then finishes the induction. The caller uses the returned Library for the
inductive branch and subsequent attempts. A missing descent or a
`Unproved` continues the scan in order. Exhausting the candidates returns
`(:failure "Unproved" "")`. Recursive invocations come
from the definition in the Library, as the index's cache can be omitted.

The following results include a library component because integer or
numeric type inference on the input terms can add lemmas. The argument
lists are the ones in the table.

| Function | Result |
|---|---|
| `quotient-proofs-product-successor` | `(step . lib)`. |
| `quotient-proofs-reciprocal-cancel` | `(step . lib)`. |
| `quotient-proofs-quotient-ratio` | `((numerator denominator numerator-integer denominator-integer denominator-positive equality) . lib)`. |

`(quotient-proofs-quotient-decrease-with-rulers lib goal rulers)`
returns `((step rulers) . lib)` with the Rulers after its hypothesis
queries. The Step is optional. A failure can appear in place of the pair.

`(quotient-proofs-dividend-rulers-with-rulers lib value base rulers)`
returns `((evidence . rulers) . lib)`, where evidence is the optional
pair of Steps specified for `dividend-rulers`.
