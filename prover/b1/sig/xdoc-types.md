# XDOC types

Terms, Steps and Libraries use the forms in `prover/sig/proof.md` and
`prover/sig/library.md`. A proof recipe takes a Library and the translated
formula to prove. An evidence argument is a list of Steps in the order
in which they are supplied. A failure takes the place of the entire result.

| ACL2 call | Arguments and result | Failure |
|---|---|---|
| `(b1-xdoc-types-xdoc name)` | ASCII name string. Returns the corresponding symbol in the `XDOC` package. | None. |
| `(b1-xdoc-types-list-type-implication lib formula)` | Proves transfer from one list recognizer to another. Returns a Step. | A failure from reading the formula or constructing the proof. |
| `(b1-xdoc-types-tree-cons lib formula)` | Proves the `TREEP` formula for a cons. Returns a Step. | A failure from reading the formula or constructing the proof. |
| `(b1-xdoc-types-tree-alist-cons lib formula)` | Proves the `KEYWORD-TREE-ALISTP` formula for a cons. Returns a Step. | A failure from reading the formula or constructing the proof. |
| `(b1-xdoc-types-tree-constructor lib formula)` | Proves a `TREEP` formula for a tree tag or directive constructor. Returns a Step. | A failure from reading the formula or constructing the proof. |
| `(b1-xdoc-types-tree-tag-wrapper lib formula)` | Proves the `TREEP` equation for a wrapper around a literal tag. Returns a Step or `nil` when the recipe does not apply. | A failure from reading the formula or constructing the proof. |
| `(b1-xdoc-types-string-value n lib value evidence)` | Fuel, Library, value term and evidence, with `nil` for omitted evidence. Returns a Step showing the value is a string. | A failure from reading the value or constructing the proof, or `Fuel`. |
| `(b1-xdoc-types-evidence-from-cases lib tests)` | Library and ordered list of `(test holds)` pairs. Returns the signed assumptions in order, splitting the conjunctions of true assumptions in order. | A failure from constructing the assumptions. |
| `(b1-xdoc-types-string-branches n lib call evidence)` | Fuel, Library, a call term and evidence. Returns a Step showing the call returns a string. | A failure from reading the call or constructing the proof, or `Fuel`. |
| `(b1-xdoc-types-string-result lib formula)` | Proves a formula for the string type of a call's result. Returns a Step. | A failure from reading the formula or constructing the proof. |
| `(b1-xdoc-types-mv-string-result lib formula)` | Proves a formula for the string type of an `MV-NTH` projection. Returns a Step. | A failure from reading the formula or constructing the proof. |
| `(b1-xdoc-types-escaped-list-type lib formula)` | Proves that a list with inserted separators retains its element type. Returns a Step. | A failure from reading the formula or constructing the proof. |
| `(b1-xdoc-types-partition-macro-args lib formula)` | Proves one of the two result types of `PARTITION-MACRO-ARGS`. Returns `(cons step lib)` with its joint type lemma installed in the Library. | A failure from reading the formula or constructing the proof. |

Pass `1000000` as the initial fuel for the mutually recursive string
proofs. The Step for a successful recipe contains the proof rules and
clause in their construction order.

The symbol constants are `*b1-xdoc-types-tree*`, `*b1-xdoc-types-trees*`,
`*b1-xdoc-types-tag*`, `*b1-xdoc-types-tree-alist*`,
`*b1-xdoc-types-make-tag*`, `*b1-xdoc-types-make-directive*`,
`*b1-xdoc-types-keywordp*`, `*b1-xdoc-types-acons*` and
`*b1-xdoc-types-alistp*`. The set `*b1-xdoc-types-string-constructors*`
lists its symbols in ascending order of their serialized forms.

The result of `b1-xdoc-types-escaped-list-type` is `(cons step lib)`.
The Library carries any lemmas installed while typing a character list.
