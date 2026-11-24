# Focused book proofs

`proof` is the H2 proof search object used for book statements. Terms and
Steps follow `prover/sig/proof.md`. Failure values follow `prover/FAILURES.md`.
`formula` is the translated theorem formula, `name` is its symbol datum in
`focused-proof`, and `label` is the ASCII theorem name without its package.

Each call can return a failure. A successful call returns `(cons value proof)` with the
resulting proof object and any facts, entries, and search settings established
by the call. A recipe that does not apply has `nil` as its value. Sequences of
definitions, facts, assumptions, and bindings preserve their supplied order.

| Function | Arguments in order | Value |
|---|---|---|
| `h2-book-recipes-focused-proof` | `proof`, symbol `name`, `formula` | The first Step obtained by the focused recipes, or `nil`. |
| `h2-book-recipes-append-equation` | `proof`, `formula` | An append equation Step, or `nil`. |
| `h2-book-recipes-append-recognizer` | `proof`, `formula` | A Step lifting an element recognizer through append, or `nil`. |
| `h2-book-recipes-injective-intern` | `proof`, `formula` | A Step using the symbol-name inverse of intern. |
| `h2-book-recipes-injective-intern-inverse` | Name term, Step proving that name is a string, `proof`, package term, Step proving that package's namespace condition | A Step for the symbol-name inverse at the given term. |
| `h2-book-recipes-make-list-recognizer` | `proof`, `formula` | A Step for the true-list recognizer of `MAKE-LIST-AC`. |
| `h2-book-recipes-gentle-take` | `proof`, `formula` | A Step for the true-list recognizer of `GENTLE-TAKE`. |
| `h2-book-recipes-remove-one` | `proof`, ASCII theorem label, `formula` | A Step for the given `REMOVE1-EQUAL` theorem. |
| `h2-book-recipes-array-fields` | `proof`, condition Step for `ARRAY1P` | The list of Steps for the header and dimensions checks, in forward-theorem order followed by linear-theorem order. |
| `h2-book-recipes-compressed-header` | `proof` | The ASCII fact name `SELF-H2-HEADER-OF-COMPRESS1`, after adding the fact if absent. |
| `h2-book-recipes-array-proof` | `proof`, `label`, `formula` | A Step for a focused array theorem, or `nil`. |

The BookProof is owned by `books.lisp`, which comes after this book in
`prover/h2/ORDER`. The focused entry point requests BookProof operations from
its caller. `(h2-book-recipes-focused-proof-with-replies proof name formula
replies)` takes the same inputs as the focused entry point, plus the ordered
list of replies. Use `nil` for the first call. An unanswered operation returns
`(:h2-book-recipes-request operation proof args)`. The functions
`h2-book-recipes-request-p`, `h2-book-recipes-request-operation`,
`h2-book-recipes-request-proof`, and `h2-book-recipes-request-args` recognize
the request or return its fields. Append each reply and repeat the call with
its original proof, name, and formula.

A reply is `(cons value proof)` with the BookProof after the operation. The
value of a procedure is `nil`. A reply may put a failure in the value position
when the operation updates BookProof before returning the failure. The reply-aware
entry point returns an `Unproved` in the value position so the caller can
retain the BookProof for the rest of the theorem search.

| Operation | Arguments in order | Value |
|---|---|---|
| `:library` | None | Inherited Library. |
| `:list-rules` | None | Ordered true-list rule names. |
| `:configure` | Definitions, facts, repeat, split limit | `nil`. |
| `:configure-book` | Definitions, repeat, facts, dynamic | `nil`. |
| `:induct-with-folded-calls` | Formula, variable, definitions | Induction Step. |
| `:keep-folded` | Terms | Saved fixed calls, with the returned BookProof using the union. |
| `:restore-fixed-calls` | Saved fixed calls | `nil`. |
| `:derive` | Formula, definitions, facts, variable, depth, repeat, seeds, cases, split limit | Step. |
| `:auxiliary` | Name, formula, definitions, facts, variable, depth, repeat, seeds, cases, split limit | Fact name string. |
| `:solve` | Formula, seeds, cases | Step. |
| `:lemma` | Name, claim, Step, conditions | `nil`. |
| `:search` | Recipe keyword, then its arguments after `proof` | The selected recipe's value. |

`(h2-book-recipes-search-call search recipe args)` dispatches a `:search`
operation on the inherited Search. The arguments in `args` follow the
selected recipe's signature. Its result is `(cons value search)`, a search
request, or a failure. The keyword selects the recipe. An enclosing search driver can use this call with its
Search hooks and retain the updated Search in the BookProof.

| Additional operation | Arguments in order | Value |
|---|---|---|
| `:recipes` | Recipe keyword, then its arguments after `proof` | The selected recipe's value. |
| `:compression-lookup-theorem` | Label, formula | The compression lookup Step. |
| `:compressed-aref` | Formula | The compressed array read Step. |

`(h2-book-recipes-recipes-call recipes recipe args)` dispatches a `:recipes`
operation on the inherited Recipes. Its result is `(cons value recipes)`,
a search request, or a failure. If `:numeric-theorem` returns a folded
induction request in the value position, apply that request with the
returned Recipes installed before replying to the focused recipe. The
compression operations use `h2-compression-lookup-call-with-replies` with
the current BookProof and the same operation name.

`(h2-book-recipes-call-with-replies proof recipe args replies)` applies the
same reply protocol to any recipe above, with its arguments other than
`proof` in `args`. Defaults and argument order match the corresponding call.

A `:recipes` reply may also return a folded induction request from
`:numeric-theorem` as its value. The focused recipe will then request
`:induct-with-folded-calls` on the BookProof in that reply.

The two dispatch forms are ACL2 macros that expand in the book prover.
The Recipes dispatcher presents a folded induction value as
`(:h2-book-recipes-folded-induction formula variable definitions)`, which
can be passed to the focused recipe with the updated BookProof in the reply.
