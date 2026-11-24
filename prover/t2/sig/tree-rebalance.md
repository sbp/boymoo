# Symbol tree rebalancing

A Library and a Step have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. The symbol constants are `*t2-tree-rebalance-build-tree*`,
`*t2-tree-rebalance-rebalance*`, `*t2-tree-rebalance-length*` and
`*t2-tree-rebalance-stringp*`.

| ACL2 call | Arguments and result | Failure |
|---|---|---|
| `(t2-tree-rebalance-prefixes seq n)` | Two terms selecting the tree and the remaining alist from the build call for terms `seq` and `n`. | None. |
| `(t2-tree-rebalance-prefix-properties seq n)` | The four terms expressing the type, length and reconstruction properties for those projections, in that order. | None. |
| `(t2-tree-rebalance-positive-length lib strictly-positive)` | A Step proving that the list is a cons, given a Step that its length is strictly positive. | May fail. |
| `(t2-tree-rebalance-length-after-tail lib nonempty)` | A Step expressing the length of the tail, given a Step that the list is a cons. | May fail. |
| `(t2-tree-rebalance-publish lib aux known)` | A Step joining the four property Steps in `known`, transported to the projections of the build call by the equality Step `aux`. | May fail. |
| `(t2-tree-rebalance-simplify-build lib n known)` | An equality Step reducing the build call for `X` and term `n` under the Step list `known`. Pass `nil` for the default `known`. | May fail. |
| `(t2-tree-rebalance-expand-constructor term)` | The expansion predicate for a constructor application under the tree predicate, inorder traversal or append. | May fail. |
| `(t2-tree-rebalance-short-prefix lib size typed lower-bound claim)` | The prefix property Step for integer `size` zero or one, with alist and length-bound Steps and the claim term. | May fail. |
| `(t2-tree-rebalance-long-prefix lib formula typed size nonnegative enough)` | `(cons (list step substitutions) lib)` with the recursive case Step, the ordered pair of substitution lists and the updated Library. `formula` is the induction formula and the four remaining arguments are premise Steps. | May fail. |
| `(t2-tree-rebalance-prefix-invariant lib)` | `(cons name lib)` with the name of the prefix-invariant lemma and the updated Library. | May fail. |
| `(t2-tree-rebalance-proper-length lib typed)` | An equality Step for `LENGTH` of the list proved to be a true list by `typed`. | May fail. |
| `(t2-tree-rebalance-rebalance-consequences lib)` | `(cons name lib)` with the name of the rebalance-invariant lemma and the updated Library. | May fail. |
| `(t2-tree-rebalance-rebalance-lookup lib formula)` | `(cons step lib)` with the lookup-preservation Step for the formula and the updated Library. | May fail. |
| `(t2-tree-rebalance-prove lib formula)` | `(cons step lib)` with the proof Step for a recognized formula or `nil` in the car, and the updated Library in the cdr. | May fail. |

A failure is the entire result. A lemma name returned by these functions is
an unprefixed string. Substitution lists use `(variable term)`
pairs in the order in which the induction hypothesis supplies them.

The reductions in `simplify-build`, `short-prefix` and `proper-length`
can add lemmas through structural proof recipes. Each of these functions
returns `(cons step lib)` with the Step described above and the resulting
Library. A failure is the entire result.

`(t2-tree-rebalance-prove-attempt lib formula)` takes the arguments of
`prove` and returns `(cons step-or-failure lib)`. The proof position is a
Step, `nil` for an unrecognized formula, or the failure from the attempted
proof. The Library retains lemmas added before the result was reached.
Use this entry point when a caller catches `Unproved` and continues with
the Library.
