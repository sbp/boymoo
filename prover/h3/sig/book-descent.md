# Descent proofs for book definitions

A Library, Step, term, Call and definition have the forms in `prover/sig/`.
Aids are a list of `(kind fields)` records in source order. A measure map is
an insertion-ordered alist from function names to measure terms. A `nil`
Call denotes an ordinality obligation.

| ACL2 call | Arguments and result | Failure |
|---|---|---|
| `(h3-book-descent-match-descent actual formal)` | An actual term and a formal term. Returns a Boolean. | A failure from inspecting the term or its logical body. |
| `(h3-book-descent-signed-hypotheses lib call)` | Library and a Call. Returns assumption Steps in signed-test order. | A failure from constructing an assumption. |
| `(h3-book-descent-prove-under-rulers lib conclusion evidence)` | Library, conclusion term and evidence Step list. Returns a Step. | A failure from proof search. |
| `(h3-book-descent-set-fix-type lib formula)` | Library and theorem formula. Returns a Step. | A failure from constructing the proof. |

Where a result contains a Library, it has the definitions and lemmas
registered during the call. A failure is the entire result.

The constants are `*h3-book-descent-zp*`, `*h3-book-descent-selectors*`,
`*h3-book-descent-transparent*`, `*h3-book-descent-support*`,
`*h3-book-descent-set-empty*`, `*h3-book-descent-set-fix*`,
`*h3-book-descent-set-type*` and `*h3-book-descent-set-selectors*`.
The selector set lists CAR and CDR in that order. The set-selector map
lists HEAD before TAIL. The support rule names follow their declared order.

`(h3-book-descent-set-selector-theorem-with-library lib formula)` and
`(h3-book-descent-termination-proof-with-library lib fields aids proof-entry)`
return the usual result pair on success. On a failure they return
`(cons failure lib)` so the caller can retain entries registered before
the failure.
