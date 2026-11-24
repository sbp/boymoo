# Lexer suffix proofs

A LexerProofs object is `(:lexer-proofs lib induction)`. The Library is
described in `prover/sig/library.md`. The induction record is `nil` outside
induction and otherwise `(function formals formula measure substitutions)`.
The substitutions are lists of binding pairs in order of first encounter.
The constructors and accessors below give these fields. Terms, Steps and
Hypotheses use the shared representations.

`*lexer-plain*`, `*lexer-quoted*`, `*lexer-part*`, `*lexer-symbol-rest*`,
`*lexer-sharp*` and `*lexer-atom*` are lexer function symbols.
`*lexer-fields*` maps these symbols to lists of output and input suffix
depths, in that order of insertion.

| Call | Arguments and result | Failure |
|---|---|---|
| `(lexer-tail term n)` | Form a chain of `n` `CDR` applications to the term. | None for natural `n`. |
| `(lexer-length term)` | Form the `LEN` application to the term. | None. |
| `(lexer-lexer-proofs-init lib)` | Construct LexerProofs from Library `lib`. | None. |
| `(lexer-lexer-proofs-lib lexer)` | Return the Library of LexerProofs `lexer`. | None. |
| `(lexer-lexer-proofs-induction lexer)` | Return its induction record. | None. |
| `(lexer-lexer-proofs-cite lexer call suffix)` | Instantiate the suffix fact for the lexer call. Pass the empty string for the default suffix. | Missing definition or proof construction. |
| `(lexer-lexer-proofs-selectors lexer term)` | Return the equality Step reducing explicit selectors, or `nil`. | Malformed term, proof construction or fuel. |
| `(lexer-lexer-proofs-replace-endpoint lexer step equality lower)` | Rewrite the lower endpoint of the comparison Step if `lower` is true, and the upper endpoint otherwise. | Failed assertion or proof construction. |
| `(lexer-lexer-proofs-relation lexer rest source hypotheses)` | Return `(step lexer hypotheses)` for the bound from the suffix term `rest` to the term `source`, with the resulting objects. | Missing path, cycle, proof construction or fuel. |
| `(lexer-lexer-proofs-suffix-edge lexer rest hypotheses)` | Return `(step parent lexer hypotheses)` for one suffix edge from the term `rest`. | Missing bound or proof construction. |
| `(lexer-lexer-proofs-lexed-suffix lexer call hypotheses)` | Return `(step lexer hypotheses)` for the suffix bound of the lexer application `call`. | Missing evidence or proof construction. |
| `(lexer-lexer-proofs-plain-test lexer call hypotheses)` | Return `(cons step hypotheses)` for the starting test of a plain scan, with a `nil` Step if no evidence was found. | Malformed term or proof construction. |
| `(lexer-lexer-proofs-implication lexer antecedent result)` | Prove the implication with the given antecedent term and consequent Step. | Proof construction. |
| `(lexer-lexer-proofs-result-branch lexer function source value tests template)` | Return `(cons step lexer)` for one result branch of the lexer function, with source term, branch value term, ordered signed tests and formula template. | Missing bound, proof construction or fuel. |
| `(lexer-lexer-proofs-prove-result lexer function induct)` | Return LexerProofs with the result lemma for the named lexer function. The Boolean `induct` selects induction and defaults to `nil`. | Missing definition, failed proof construction or fuel. |
| `(lexer-lexer-proofs-prove-plain-strict lexer)` | Return LexerProofs with the strict plain-scan bound. | Missing definition, failed proof construction or fuel. |
| `(lexer-lexer-proofs-build lexer)` | Return LexerProofs with all seven suffix lemmas appended to its Library in construction order. | Failed proof construction or fuel. |
| `(lexer-lexer-proofs-decrease lexer goal hypotheses)` | Return `(step lexer hypotheses)` for the ordinal comparison `goal` using the length bound of its child suffix. | Missing bound, proof construction or fuel. |

In a result containing LexerProofs or Hypotheses objects, the returned
objects include changes made while deriving that result. Any failure is
returned in place of the entire result.
