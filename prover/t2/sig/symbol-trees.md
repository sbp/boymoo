# Proofs for symbol-keyed binary trees

A Library, term and Step have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. A test is a pair `(term holds)`, with `t` or `nil`
for `holds`. Substitutions are lists of two-element binding pairs in
the order supplied to induction.

The symbol constants are `*t2-symbol-trees-treep*`,
`*t2-symbol-trees-update*`, `*t2-symbol-trees-find*`,
`*t2-symbol-trees-to-alist*`, `*t2-symbol-trees-with-acc*`,
`*t2-symbol-trees-find-depth-acc*`, `*t2-symbol-trees-find-depth*`,
`*t2-symbol-trees-update-depth*`, `*t2-symbol-trees-update-find-depth*`,
`*t2-symbol-trees-key-depth*`, and `*t2-symbol-trees-symbolp*`.
`*t2-symbol-trees-depth-positions*` maps the four depth operations to
their zero-based tree positions in the order `FIND-DEPTH-ACC`,
`FIND-DEPTH`, `UPDATE-DEPTH`, `UPDATE-FIND-DEPTH`.

Proof recipes return `(cons value lib)` with the Library as it stands on
return and a Step, `nil`, or a failure as `value`. This preserves auxiliary
lemmas if the caller handles a failure. In `prove`, `nil` means that
the formula matched no recipe.

| ACL2 call | Arguments and result |
|---|---|
| `(t2-symbol-trees-children tree)` | Given a term, its left and right child terms in that order. |
| `(t2-symbol-trees-update-preserves-type lib formula)` | Proof of preservation of tree type by update. |
| `(t2-symbol-trees-lookup-after-update-solve-test same lib formula tree branch nonempty same-key steps)` | Proof of a lookup case, given the Boolean indicating whether keys match, the formula and tree terms, the branch test term and its Boolean, the key equality term, and the induction Steps. |
| `(t2-symbol-trees-lookup-after-update lib formula)` | Proof of lookup after update. |
| `(t2-symbol-trees-alist-accumulator lib formula)` | Proof of the accumulator equation for conversion to an alist. |
| `(t2-symbol-trees-alist-type-case has-entry lib result conversion predicate tree tests entry facts smaller-types name first remainder)` | Proof of the conversion type in the branch selected by `has-entry`. The terms give the result, conversion, predicate, tree, entry test and two recursive conversions. `tests`, `facts` and `smaller-types` are ordered tests and evidence Steps, and `name` is the append preservation lemma name. |
| `(t2-symbol-trees-alist-type lib formula)` | Proof of the list type of a tree conversion. |
| `(t2-symbol-trees-aligned-depth lib formula)` | Proof that the depth operation agrees with the associated tree operation and key depth. |
| `(t2-symbol-trees-prove lib formula)` | Proof by the first matching tree recipe, or `nil`. |
