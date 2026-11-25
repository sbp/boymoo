# List maps and folds

`lib` is a Library as specified in `prover/sig/library.md`. Terms and Steps use the forms in `prover/sig/proof.md`. An equality Step has an equality as its first literal. Evidence and definitions are ordered lists of Steps and function names, respectively. A binding is a two-element list `(variable value)`.

`*t3-book-spines-guards*` lists the guard symbols `ATOM`, `ENDP`, `NULL`, `EQ`, `EQL` and `NOT` in that order. Pass it for the default definitions in `constructor-form`. Pass `nil` for omitted evidence in `shallow`.

| ACL2 call | Result | Failure |
|---|---|---|
| `(t3-book-spines-constructor-form lib value evidence definitions)` | Tidy equality Step for the normalized constructor form of term `value`, or `nil` when there is no equation. | A failure from normalization or proof construction, or `fuel`. |
| `(t3-book-spines-shallow lib term evidence)` | Equality Step chaining one unfolding of `term` with its constructor form. | A failure from unfolding, normalization or proof construction. |
| `(t3-book-spines-replace-value lib equation replacements)` | Equality Step after applying the equality Steps in `replacements` in order to the right side of `equation`. | A failure from proof construction. |
| `(t3-book-spines-tail-bindings lib call)` | The changed argument bindings, in argument order, when every recursive call has the same substituted actuals and each changed argument occurs once. An empty binding list is `nil`. | A failure from looking up the definition, walking the calls or substituting. |
| `(t3-book-spines-map-parameter lib call)` | The single variable traversed by `CDR`, or `nil` when the recursion does not have that form. | A failure from walking the calls or indexing a malformed call. |
| `(t3-book-spines-mapped-list lib formula solve)` | A proof Step for the mapped-list result or length, `nil` when inapplicable, or a callback request. | A failure from reading terms, proof construction or the callback. |
| `(t3-book-spines-fold-over-list-fix lib formula)` | A proof Step that the fold ignores the list fix, or `nil` when inapplicable. | A failure from reading terms or proof construction. |
| `(t3-book-spines-car-of-fix lib fix variable)` | A proof Step that `CAR` is preserved by term `fix` on `variable`, or `nil` when inapplicable. | A failure from reading terms or proof construction. |
| `(t3-book-spines-commuting-list-fix lib formula rewriting)` | A proof Step for a list fix commuting with a changing argument, `nil` when inapplicable, or a callback request. | A failure from reading terms, proof construction or the callback. |
| `(t3-book-spines-removal-over-list-fix lib formula)` | A proof Step for moving a list fix through removal, or `nil` when inapplicable. | A failure from reading terms or proof construction. |
| `(t3-book-spines-absence lib formula)` | A proof Step that a missing key has zero occurrences or that its removal preserves a proper list, or `nil` when inapplicable. | A failure from reading terms or proof construction. |
| `(t3-book-spines-different-key lib formula)` | A proof Step that a fold testing one key ignores removal of a different key, or `nil` when inapplicable. | A failure from reading terms or proof construction. |

`solve` and `rewriting` are lists of callback replies in invocation order. Start with `nil`. When execution needs the next reply, it returns `(:callback :solve term evidence)` or `(:callback :rewriting term)`. Evaluate the callback in the caller and rerun the original call with the reply appended. A reply is a Step, `nil` or a failure. The list has one entry per invocation, including invocations that return `nil`. `t3-book-spines-callback-p`, `t3-book-spines-callback-kind` and `t3-book-spines-callback-args` recognize a request or return its kind or ordered argument list, respectively.

The `lib` argument can also be the book proof context in `prover/t3/sig/book-values.md`. Its package declarations are available to primitive computations. A Library with the `:t3-book` Proof dispatch tag supports the primitive computations that need no package declarations.

`(t3-book-spines-library-simplify lib term evidence definitions)` uses the primitive computation rules for `lib`. It returns a simplification Step, `nil` or a failure, including `fuel`. `(t3-book-spines-proof lib)` returns the Proof used for inference.

The book proof context constructor and fields are also available as `t3-book-spines-make-book-proofs`, `t3-book-spines-library`, `t3-book-spines-book-packages` and `t3-book-spines-book-visible`. The library accessor accepts either a book proof context or a Library. 
The book proof context primitive operations are available as `t3-book-spines-tagged`, `t3-book-spines-book-package-value`, `t3-book-spines-book-coerce`, `t3-book-spines-book-constant` and `t3-book-spines-book-simplify`. Their arguments, results and failures are those of `tagged` and the corresponding methods in `prover/t3/sig/book-values.md`. The eleven primitive symbol constants in that signature also have names with `t3-book-spines` in place of `t3-book-values`.
