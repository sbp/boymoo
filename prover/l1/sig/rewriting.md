# Equation rewriting and induction

Terms, Steps and Proofs have the forms in `prover/sig/proof.md`. Bindings, evidence maps and premises maps are insertion-ordered alists. The keys of evidence and premises are terms, and their values are Steps. A premise list, where specified, is a list of Steps in the supplied order. Set `split` to the branch budget, using `0` to disable splitting. A returned failure replaces the entire result.

An Equation is `(:equation name pattern replacement hypothesis reverse can-expand)`. The name, pattern and replacement are prover data. The hypothesis is a term or `:none`. The last two fields are Boolean. Each field is available through the corresponding accessor `l1-rewriting-equation-name`, `l1-rewriting-equation-pattern`, `l1-rewriting-equation-replacement`, `l1-rewriting-equation-hypothesis`, `l1-rewriting-equation-reverse`, and `l1-rewriting-equation-can-expand`. The accessors return their values directly.

A Rewriter is `(:rewriter proof equations propositions structural)`. The equations alist maps call heads to lists of Equations in the order the constructor examines their directions. The propositions alist maps call heads to lists of `(name pattern hypothesis)` in fact order. The structural alist maps function names to `(position descending)` in fact order, with recursive calls in traversal order. These alists retain the insertion order of their keys. Their accessors are `l1-rewriting-rewriter-proof`, `l1-rewriting-rewriter-equations`, `l1-rewriting-rewriter-propositions`, and `l1-rewriting-rewriter-structural`. The accessors return their values directly.

| Function | Arguments and result | Failure |
|---|---|---|
| `(l1-rewriting-match pattern term bindings)` | `(cons matched-p updated-bindings)` with bindings in insertion order, including new bindings encountered before a mismatch. | A failure from matching an empty compound term or a malformed subterm. |
| `(l1-rewriting-size term)` | The number of nodes, treating quoted terms and atoms as one node. | None. |
| `(l1-rewriting-calls term)` | The unquoted compound terms visited in preorder, descending through actual arguments. | None. |
| `(l1-rewriting-structural-argument name definition)` | `(position descending)` giving the argument position and distinct descending calls in traversal order, or `nil`. `definition` is `(formals body)`. | A failure from accessing a malformed term. |
| `(l1-rewriting-recursive-substitution formals call recursive-call)` | The ordered list of `(variable term)` binding pairs under which `call` agrees with `recursive-call`, or `nil`. | A failure from substitution. |
| `(l1-rewriting-rewriter-init proof)` | The Rewriter indexing the Proof's admitted equations and propositions. | A failure from inspecting a fact or a definition. |
| `(l1-rewriting-rewriter-derive rewriter term evidence depth trail)` | A Step for an admitted proposition, or `nil`. `depth` defaults to `3` and `trail` is the set of already visited terms, empty by default. | A failure from proof construction, term traversal, or `fuel`. |
| `(l1-rewriting-rewriter-branch rewriter term evidence)` | The equality Step selecting a branch of conditional `term`, or `nil`. | A failure from proof construction. |
| `(l1-rewriting-rewriter-structural-branch rewriter term evidence)` | The equality Step opening a recursive call whose outer test can be decided, or `nil`. | A failure from proof construction or `fuel`. |
| `(l1-rewriting-rewriter-at-root rewriter term evidence)` | The equality Step rewriting `term` at its root, or `nil`. | A failure from proof construction. |
| `(l1-rewriting-rewriter-redex rewriter term evidence place)` | `(place step)` for the first rewrite from the given starting place, or `nil`. | A failure from proof construction or term traversal. |
| `(l1-rewriting-rewriter-premises rewriter evidence)` | The insertion-ordered premises map after processing the given premise list as a stack. | A failure from proof construction or `fuel`. |
| `(l1-rewriting-rewriter-prove rewriter formula evidence split)` | A Step proving `formula` from the given premise list. | `unproved`, `fuel`, or a failure from proof construction. |
| `(l1-rewriting-rewriter-rewrite rewriter formula premises split)` | A Step proving `formula` from the given premises map. | `unproved`, `fuel`, or a failure from proof construction. |
| `(l1-rewriting-rewriter-induct rewriter formula)` | A Step proving `formula` by structural induction. | `unproved` if no plan succeeds, or a failure from proof construction. |
| `(l1-rewriting-rewriter-induct-on rewriter formula variable substitutions)` | A Step proving `formula` by induction on `variable`. `substitutions` is the ordered list of binding lists for the recursive calls. | A failure from proof construction or an absent binding. |

The constants are `*l1-rewriting-atom*`, `*l1-rewriting-endp*`, and `*l1-rewriting-descent*`. The descent alist orders `CAR` before `CDR`.

| Function | Arguments and result | Failure |
|---|---|---|
| `(l1-rewriting-prepare proof)` | An index for the Proof's current facts and definitions, for use with `l1-rewriting-update-prepared` and `l1-rewriting-rewriter-prepared`. | None. |
| `(l1-rewriting-update-prepared index proof names)` | The index updated for the given Proof. `names` lists all facts written since the input index, in write order. A replacement retains its position in fact order. | None. |
| `(l1-rewriting-rewriter-prepared proof index)` | A Rewriter for the indexed Proof. Each call head has rules in the order used by `l1-rewriting-rewriter-init`. | The first failure that `l1-rewriting-rewriter-init` would return for the same Proof. |
