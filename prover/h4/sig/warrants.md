# Warrant proofs

`p` is the Tactics object defined in `tactics.md`. Formulae and Steps use the forms in `prover/sig/proof.md`. A failure occupies the entire result.

| ACL2 call | Result and failures |
|---|---|
| `(h4-warrants-warrant-parts formula)` | The pair `(function necessity)` as a two-element list of symbol data, or `nil` for an unmatched formula. Malformed fields can return a failure. |
| `(h4-warrants-tame-example p)` | A Step proving that the fixed lambda is tame. May return a failure. |
| `(h4-warrants-proved-warrant p formula primitive-absence witness)` | A Step proving the warrant `formula`, using the primitive-absence Step and the tame-witness Step. May return a failure. |
| `(h4-warrants-warrant-recipe p formula warrant-filters)` | `(cons step p)` with the warrant proof and the Tactics object containing any added propositional lemmas. `warrant-filters` is the list of definition names supplied by the prepared certificate. May return a failure. |

The symbol constants are `*h4-warrants-primitive*`, `*h4-warrants-tame*`, `*h4-warrants-filter*`, `*h4-warrants-primitive-absence*`, `*h4-warrants-tame-example*`, `*h4-warrants-key*`, `*h4-warrants-eq*`, `*h4-warrants-force*`, `*h4-warrants-badge*`, and `*h4-warrants-apply*`. `*h4-warrants-example*` is the lambda datum.

`(h4-warrants-datum-length datum)` returns the length of a list or an ASCII string. A numeric datum or `t` gives a failure.
