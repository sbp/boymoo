# Lexicographic comparison proofs

`lib` is the tactic library. Terms and Steps use the forms in `prover/sig/proof.md`. Each call may return a failure in place of the listed result.

| Call | Arguments and result |
|---|---|
| `(b2-lexicographic-type-fact lib a b value disjoint)` | Step naming the relation between type symbols `a` and `b` on term `value`. Pass `nil` for the ordinary implication and `t` for disjoint types. |
| `(b2-lexicographic-exclude-types lib value kind assumed)` | List of Steps excluding other types of `value` in traversal order, given the type symbol `kind` and its Step `assumed`. |
| `(b2-lexicographic-exclude-number lib value kind typed)` | Step excluding numbers for `value` given its nonnumeric type symbol `kind` and corresponding Step `typed`. |
| `(b2-lexicographic-atom-types lib value replies)` | Step assembled from the callback Steps for the type cases of `value`. `replies` is an alist with `(kind evidence)` keys and Step or failure values. At the first missing reply the result is `(:b2-lexicographic-atom-types kind evidence)`. Supply that reply and repeat the call. |
| `(b2-lexicographic-atom-comparison lib formula base)` | Step proving the comparator equality `formula`, given the list `base` of Steps that its arguments are atoms. |
| `(b2-lexicographic-lexorder-equivalence lib formula)` | Tree induction Step proving the comparator equality `formula`. |

In the type callback, `kind` is the type predicate symbol and `evidence` is the ordered list of Steps for that case. The rational cases visit integer before noninteger. The other types follow in the order in `*b2-lexicographic-atom-types*`. The final case uses `nil` for `kind` and supplies evidence excluding those types.

The constants are `*b2-lexicographic-alpha*`, `*b2-lexicographic-symbol-less*`, `*b2-lexicographic-complex*`, `*b2-lexicographic-string*`, `*b2-lexicographic-atom-types*` and `*b2-lexicographic-disjoint*`.
