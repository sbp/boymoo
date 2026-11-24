# Selector descent proof signatures

`lib` is a library, `step` is a proof step and `rulers` is a `Rulers` object. An edge is `(selector parent)`, with the edges ordered from the root to the descendant. All functions can return a failure in place of their result.

| ACL2 call | Arguments and result |
|---|---|
| `(selector-proofs-count-cons-lemmas lib)` | Adds the count equations for conses and returns the resulting library. |
| `(selector-proofs-grouped-count lib actual siblings)` | `actual` and `siblings` are terms, with at least one term in the sibling list. Returns `(rest step)` where `rest` is the grouped sibling term and `step` expands the count of `(CONS actual rest)`. |
| `(selector-proofs-regrouped-descent lib actual edges evidence)` | `actual` is the descendant term. `evidence` is a list of proofs that the edge parents are conses. Returns `(cons step lib)` with a strict count comparison. |
| `(selector-proofs-count-nil-bound lib)` | Adds the count comparison between nil and a cons and returns the resulting library. |
| `(selector-proofs-nil-path-descent lib edges root-cons start)` | `root-cons` proves the root is a cons. `start` is the zero-based index of the first parent assumed to be an atom. Returns `(cons step lib)` with a strict count comparison. |
| `(selector-proofs-selector-path-descent lib actual edges rulers)` | `actual` is the descendant term. Returns `(cons step lib)` with a strict count comparison or a nil step if the path is too short or a root cons proof is unavailable. |
| `(selector-proofs-selector-path-descent-descend n evidence lib actual edges initial)` | Splits on missing cons proofs in `evidence`. `initial` is the original list of optional cons proofs. Returns `(cons step lib)` and can return a `Fuel` failure. |

`(selector-proofs-selector-path-descent-with-rulers lib actual edges rulers)` takes the same arguments as `selector-proofs-selector-path-descent` and returns `(cons (list step rulers) lib)` or a failure. The returned Rulers holds the evidence established during the queries.
