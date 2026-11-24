# Structural list induction

`lib` is a B2 tactics library. Terms and Steps follow `prover/sig/proof.md`.
Lists of variables, steps, rules and unfoldings keep their traversal order.

| Call | Result | Failure |
|---|---|---|
| `(b2-structural-list-variables lib formula)` | Up to two variable terms, decreasing by count of cdr recursion positions. Ties keep the order of first discovery. | Failure from traversing definitions or recursive calls. |
| `(b2-structural-expand-branch lib goal x evidence rules)` | A normalization equality for goal term `goal` at variable `x` using the evidence Steps and rewrite-rule Steps, or `nil` when unchanged. Pass `nil` for omitted rules. | Failure from normalization or chaining. |
| `(b2-structural-antecedent-evidence lib antecedent x branch)` | The evidence Steps in insertion order obtained from antecedent Step `antecedent`, variable `x`, and branch Step `branch`. | Failure from collecting or rewriting evidence. |
| `(b2-structural-induction-at lib formula x)` | A Step for `formula` by list induction on `x`. | Failure from the branch search or induction. |
| `(b2-structural-list-induction lib formula)` | A Step for `formula` from the first successful list induction. | `Unproved` when no candidate succeeds, or a failure from traversal or induction. |
