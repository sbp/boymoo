# Keyword lookup

`lib` is a Library. Terms and Steps use the forms in `prover/sig/proof.md`. An argument named for a condition is its Step. Each function can return a failure in place of its result.

The constants are `*b2-keywords-assoc*`, `*b2-keywords-keywords*`, `*b2-keywords-key*` and `*b2-keywords-keywordp*`.

| ACL2 call | Result |
|---|---|
| `(b2-keywords-lookup-property lib)` | `(cons label lib)` with the lookup property lemma installed. |
| `(b2-keywords-length-at-least-two lib term cons-step tail-cons)` | Step proving the length bound given the cons tests on the term and its tail. |
| `(b2-keywords-derive lib goal result found proof)` | Step for `goal` using the lookup result term, its successful lookup Step and the result property Step. |
| `(b2-keywords-assoc-keyword lib name formula)` | `(cons step lib)` with the proof of the named keyword lookup theorem and any added lookup property lemma. |
