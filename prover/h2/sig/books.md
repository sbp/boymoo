# Books

A parsed line is `(raw kind data)`, where `raw` is the source string with its line terminator, `kind` is the statement word string, and `data` is the list of frozen fields. Terms, Steps, and Library entries follow `prover/sig/proof.md` and `prover/sig/library.md`. `recipes` and `search` are the inherited objects specified in `prover/h2/sig/recipes.md` and `prover/h2/sig/search.md`.

A RuleIndex is `(:h2-rule-index claims equations formulas)`. The three fields are insertion-ordered alists. Each key is a signature of a term, and each bucket preserves the order of insertion. The claims and equations contain Rules. The formulas contain `(name formula)` records. `h2-books-make-rule-index` takes the three fields in order. `h2-books-rule-index-claims`, `h2-books-rule-index-equations`, and `h2-books-rule-index-formulas` take an index and return the indicated field.

A BookProof is `(:h2-book-proof recipes fuel dynamic arithmetic fixed-calls library-rules book-rules packages list-rules math-rules names-as-written)`. `fuel` is an integer or `nil` for no rewriting budget. `dynamic` and `arithmetic` are Booleans. `fixed-calls` and `names-as-written` are ordered sets. Fixed calls use `h2-search-data-text` as the sort key. Written names are sorted by their escaped strings with the closing quote appended. `packages` is an insertion-ordered alist from package name strings to `(imports hidden-p)`, where `imports` preserves the input order. `list-rules` and `math-rules` are lists of fact names in recipe order. `h2-books-make-book-proof` takes the fields in order. The accessor for each field is `h2-books-book-proof-` followed by its field name. `h2-books-book-proof-search` and `h2-books-book-proof-library` give the inherited Search and Library, and `h2-books-book-proof-names` gives the Recipes name map. `h2-books-book-proof-with-recipes`, `h2-books-book-proof-with-search`, `h2-books-book-proof-with-library`, `h2-books-book-proof-with-fuel`, `h2-books-book-proof-with-fixed-calls`, and `h2-books-book-proof-with-book-rules` each take a BookProof and its replacement field value and return the BookProof with that field set.

`h2-books-book-proof-prepare-calls` takes a BookProof and attaches an index of
its definitions and their recursive calls. `h2-books-book-proof-note-definition-calls`
takes a prepared BookProof and the definition records from a newly admitted
line and records their calls. Both return the BookProof with an optional
final field `(:h2-recursions (name definition calls) ...)`. A stored failure is
returned only if the associated definition is queried. `h2-books-prepared-calls-of`
takes the same arguments as `h2-books-book-proof-calls-of`. It uses an entry
whose definition still matches the active definition.

A ContextEvidence is `(:h2-context-evidence proof context)`. Its arguments to `h2-books-context-evidence-init` are a BookProof and a Search Context. `h2-books-context-evidence-proof` and `h2-books-context-evidence-context` return its fields.

`proof` is a BookProof and `context` is a Search Context. `active` is the ordered list of active rules or search markers. `opened` is the list of calls already opened on the current path. `definitions` and `repeat` in the book configuration calls are lists of function symbols, and `facts` is a list of rule names in supplied order. `measures` maps function symbols to the fields following the name in a measure aid. `hints` maps obligation names to their ordered lists of symbols. The maps preserve key insertion order. Every argument is explicit.

| Call | Result | Failure |
|---|---|---|
| `(h2-books-calls-in term)` | List of calls in traversal order, opening a lambda body before traversing the actuals and excluding quotations. | Malformed lambda or empty compound term. |
| `(h2-books-signature term)` | The head of `term` followed by the heads of up to two immediate arguments. The signature of a noncompound term is `(nil)`. A wildcard argument head is `nil`. | Malformed compound term. |
| `(h2-books-rule-index-init)` | Empty RuleIndex. | None. |
| `(h2-books-rule-index-add-fact index proof name)` | RuleIndex with the first formula of the fact and its rules added in source order. | A failure from reading the fact or its rules. |
| `(h2-books-rule-index-add index rule)` | RuleIndex with the rule added to each applicable bucket. | A failure from inspecting the rule. |
| `(h2-books-rule-index-candidates index term rewrite)` | Rules from the equation index when `rewrite` is true or the claim index otherwise. | A failure from computing the signature. |
| `(h2-books-rule-index-lookup index buckets term)` | Bucket contents in exact-head-then-wildcard Cartesian product order, with the unheaded bucket last. `buckets` is one of the three index maps. | A failure from computing the signature. |
| `(h2-books-context-evidence-find evidence term)` | Step for `term`, or `nil`. | A failure from looking up the term. |
| `(h2-books-book-proof-init library)` | BookProof initialized with the parsed library lines in order. | A failure from admitting statements or building proofs. |
| `(h2-books-book-proof-empty-count-bound proof)` | BookProof with the strict count bound for the empty list. | A failure from proof construction. |
| `(h2-books-book-proof-fork proof)` | BookProof with an empty book rule index. | None. |
| `(h2-books-book-proof-note-package proof kind data)` | BookProof with the package table updated on package statements. | A failure from a malformed package statement. |
| `(h2-books-book-proof-admit proof kind data)` | BookProof with the facts or definitions of the statement. | A failure from admission. |
| `(h2-books-book-proof-add-statement proof kind data)` | BookProof with the statement admitted and the package, rule, and written-name indexes updated. | A failure from adding the statement. |
| `(h2-books-book-proof-lookup proof term context)` | Step for the term, or `nil`. | A failure from constructing a Step. |
| `(h2-books-book-proof-boolean-value proof term evidence)` | Equality Step for the true Boolean value of `term` using the supplied Step. | A failure from proof construction. |
| `(h2-books-book-proof-configure-book proof definitions repeat facts dynamic)` | BookProof with the book search configuration. | A failure from configuring search. |
| `(h2-books-book-proof-keep-folded proof terms)` | BookProof for the scope of the context manager, with `terms` added to the fixed calls. Restore the input `fixed-calls` on leaving the scope. | None. |
| `(h2-books-book-proof-calls-of proof function)` | List of recursive calls from the definition of `function`, in source order. | A failure from reading the definition or computing calls. |
| `(h2-books-appropriate-descent variable term)` | Whether `term` follows selectors or adds a negative integer to the variable. | A failure from a malformed selector or quotation. |
| `(h2-books-subtraction variable term)` | Whether `term` adds a negation to the variable in the indicated argument order. | A failure from a malformed sum. |
| `(h2-books-statement-name kind data)` | Name of a theorem, definition or constraint obligation, or `nil`. | A failure from a missing field. |
| `(h2-books-find-certificate proof kind data name measures hints)` | `(cons certificate proof)` for the obligation. An `unproved` becomes a Certificate with no entries and its message as the reason. | Failure for an unsupported statement kind or a proof failure other than `unproved`. |
| `(h2-books-symbols value)` | Symbols in traversal order, including repeated occurrences. | None on reader data. |

`*h2-books-arithmetic*` lists the arithmetic facts in recipe order, `*h2-books-translation*` and `*h2-books-arithmetic-defs*` list default definition names, and `*h2-books-boolean-facts*` maps predicate symbols to fact names in declaration order. The functions that run the checker, print, or read and write files have no ACL2 entry point. The package table in `h2-books-book-proof-init` starts with the packages declared by `spec/ground.txt`.

`opened` contains function names in path order. Book and library Rule identities name their index, signature, position in the formula bucket, and position among the rules of that fact. Rules supplied to `h2-books-rule-index-add` keep their supplied identity.

| Call | Result | Failure |
|---|---|---|
| `(h2-books-book-proof-index-lemmas proof)` | BookProof with the index lemmas added using its inherited search methods. | A failure from proof construction. |
| `(h2-books-book-proof-prove-theorem proof label formula)` | `(cons step proof)` from the inherited Recipes method, including `nil` when the method does not select a proof. `label` is the unqualified ASCII theorem name. | A failure from the recipe or from search. |
| `(h2-books-book-proof-solve proof formula seeds cases)` | `(cons step proof)` from the book's search, with ordered seed Steps and case terms. | A failure in the value position retains the resulting BookProof. |

`h2-books-book-proof-index-prefix-names` takes a BookProof and the
pending source lines for a prefix. It can prepare the written-name
set as a tree for the duration of prefix admission.
`h2-books-book-proof-restore-written-names` takes the resulting BookProof
and returns it with the written-name set in its ordinary textual order.
Both calls return a BookProof on their stated inputs.
