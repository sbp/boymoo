# Equivalence of canonical values

`lib` is the Library from `prover/sig/library.md`, and terms and Steps have the
forms in `prover/sig/proof.md`. `search` is the H2 Search with its current
Library and rule configuration. `*h2-equivalence-booleanp*` is the prover
symbol `BOOLEANP`.

| ACL2 call | Result |
|---|---|
| `(h2-equivalence-equality-boolean search)` | `(cons name search)` with the Boolean equality lemma and its name as a prover symbol. The first field may be a failure. |
| `(h2-equivalence-opening-to-equal lib term)` | A Step unfolding `term` and removing wrappers until its right side is an equality, or `nil` if the unfolded term does not have that form. May return a failure. |
| `(h2-equivalence-equality-equivalence search formula)` | `(cons step search)`, with a proof of the equivalence laws, `nil` when the shape does not match, or a failure. |
| `(h2-equivalence-canonical-argument lib formula book-formulas library-formulas)` | A Step transferring the premise's equality through the changed argument, `nil` when no rule applies, or a failure. |

`book-formulas` and `library-formulas` are ordered association lists.
Their keys are `(head arg-head ...)`, with a head and up to two argument
heads, or `(nil)` for a variable. Each value is the ordered list of
two-element lists `(name pattern)` for that bucket. Candidate lookup
uses the book index first. Within each index it visits the exact and
wildcard argument-head combinations in Cartesian product order, with the
unheaded bucket last. A name is a prover symbol and a pattern is a term.

A Search operation can also return a request from an inherited method as
specified in `prover/h2/sig/search.md`. The request occupies the value position
and the caller supplies the inherited-method reply before repeating the call.
