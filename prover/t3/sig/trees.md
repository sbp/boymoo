# Bounds for constructed terms

Terms and Steps have the forms in `prover/sig/proof.md`. `lib` is a Library
with T3 proof rules. `evidence` is an Evidence object from `logic.lisp`.
In a pair `(step . evidence)`, the Evidence records the queries made by
the call. A missing Step is `nil`. A failure is the whole result.

The constants are `*t3-trees-dumb-negate*`, `*t3-trees-parse-declarations*`,
`*t3-trees-mv-nth*`, `*t3-trees-guard-index*`, and `*t3-trees-guard-count*`.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t3-trees-count-cons lib term evidence)` | Constructor term or a term known to be a cons. Returns the count expansion Step paired with the resulting Evidence. | A failure from proof construction or an evidence query. |
| `(t3-trees-folded-count lib term evidence)` | Term for a constructor tree, a quoted value, or a leaf. Returns the optional count expansion Step paired with the resulting Evidence. | A failure from proof construction or an evidence query. |
| `(t3-trees-negated-literal-bound lib)` | Returns the Library with the upper bound lemma for the count of a negated literal. | A failure from proof construction or an evidence query. |
| `(t3-trees-negated-literal-descent lib smaller larger evidence)` | Two count terms. Returns `((step evidence) . lib)` with an optional ordinal decrease Step and the resulting Evidence and Library. | `unsupported` for a different field, or a failure from proof construction or an evidence query. |
| `(t3-trees-three-cons-margin lib parent field evidence)` | Parent and field terms. Returns the strict count margin Step paired with the resulting Evidence. | A failure from proof construction or an evidence query. |
| `(t3-trees-guard-upper edcls guard)` | Declaration and guard terms. Returns the upper bound term for the guard count. | None. |
| `(t3-trees-guard-input-bound lib edcls guard new-edcls new-guard evidence)` | Original and changed declaration and guard terms. Returns the bound Step paired with the resulting Evidence. | A failure from proof construction or an evidence query. |
| `(t3-trees-guard-leaf lib field edcls guard tests)` | Field, declaration, and guard terms and an ordered list of signed tests. Returns the bound Step for a field of a declaration result. | `unsupported` for an unbounded field, or a failure from proof construction or an evidence query. |
| `(t3-trees-parsed-guard-bound lib)` | Returns the Library with the upper bound lemma for the count of the parsed guard. | A failure from proof construction, definition lookup, or an evidence query. |
| `(t3-trees-parsed-guard-descent lib smaller larger evidence)` | Two count terms. Returns `((step evidence) . lib)` with an optional ordinal decrease Step and the resulting Evidence and Library. | `unsupported` for different inputs, or a failure from proof construction or an evidence query. |

The declaration substitutions are in first-occurrence order among the
recursive leaves. Each substitution lists the changed pairs in formal
parameter order.

The returned Evidence carries the updated Library when its input Library
matches `lib`.
