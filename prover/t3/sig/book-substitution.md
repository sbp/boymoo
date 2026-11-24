# Type and arity preservation of substitutions

`lib` is a Library as in `prover/sig/library.md`. Terms and Steps use the
forms in `prover/sig/proof.md`. An `evidence` argument is the Evidence object
of `prover/t3/sig/logic.md`. An `accepted` or `typed` argument is a Step
proving an input type. `known` is an ordered list of Steps. All calls in the
tables can return a failure in place of their stated result, except `view`
and `list-goal`.

| Call | Arguments and result |
|---|---|
| `(t3-book-substitution-quoted-base lib formula)` | Step proving the term or term-list type formula by simplification. |
| `(t3-book-substitution-conditional-term-type lib)` | Library with the auxiliary lemma for term-valued conditionals. |
| `(t3-book-substitution-constant-folding lib multivalue)` | Library with the auxiliary type lemmas for constant folding. The Boolean `multivalue` selects the additional `MV-NTH` lemmas. |
| `(t3-book-substitution-list-components lib typed present)` | List of two Steps for the head and tail types from a list type Step `typed` and a cons Step `present`. |
| `(t3-book-substitution-total-list-components lib typed)` | List of two Steps for the head and tail types from the list type Step `typed`. |
| `(t3-book-substitution-parallel-lookup lib)` | Library with the parallel lookup type lemma. |
| `(t3-book-substitution-original-arguments lib accepted evidence)` | `(cons (list known step) evidence)` with the cons and nonquote Steps in `known`, then the original argument-list type Step, and the resulting Evidence. |
| `(t3-book-substitution-rebuild lib term typed correct-args same-length known)` | Type Step for `term`, using the original type Step `typed`, new argument-list type Step `correct-args`, length equality Step `same-length` and ordered proof list `known`. |
| `(t3-book-substitution-substitution lib name formula operator)` | `(cons entry lib)` with the theorem entry and the Library including auxiliary lemmas. `name` and `operator` are prover symbols and `formula` is the theorem term. |

## Term traversal

A TermTraversal or Substitution has the form `(:t3-term-traversal lib
multivalue calls environment env-proof measure substitutions targets
templates claims formula kind)`. `calls`, `targets`, `templates`, and
`claims` each list the term case before the list case. `environment` is the
shared guard term and `env-proof` its Step. `substitutions` is an alist of
`(argument . pairs)` in order of first encounter. Each `pairs` is an
ordered list of two-element `(variable term)` lists. `kind` is `:base`,
`:alist`, or `:parallel`. Use the constructors below and accessors named
`t3-book-substitution-term-traversal-` followed by the field name.

| Call | Arguments and result |
|---|---|
| `(t3-book-substitution-term-traversal-init lib calls environment multivalue)` | A TermTraversal with the two listed call terms, the shared guard term, and Boolean `multivalue`. |
| `(t3-book-substitution-term-traversal-view traversal value)` | The term `value` or its second result, according to `multivalue`. |
| `(t3-book-substitution-term-traversal-list-goal value)` | Conditional conjunction of the list type of `value` and equality of its length to the length of `X`. |
| `(t3-book-substitution-term-traversal-smaller traversal field index accepted evidence)` | `(list step traversal evidence)` for the recursive application to `(field X)` with resulting Traversal and Evidence. `field` is a selector symbol and `index` is 0 for the term claim, 1 for the list claim. |
| `(t3-book-substitution-term-traversal-smaller-at traversal argument index accepted evidence)` | The same triple for the given argument term. |
| `(t3-book-substitution-term-traversal-list-result traversal value typed evidence)` | `(list step traversal evidence)` for the list and length claim on the leaf term, with resulting Traversal and Evidence. |
| `(t3-book-substitution-term-traversal-prove traversal label replies)` | Traversal with the invariant added to its Library under string `label`, or a request for a subclass's term case. |
| `(t3-book-substitution-substitution-init lib operator)` | A Substitution for the given operator symbol. |
| `(t3-book-substitution-substitution-term-result traversal value typed evidence)` | `(list step traversal evidence)` for the type of the term leaf, with resulting Traversal and Evidence. |

The `:base` traversal uses callbacks for term leaves. A request has the
form `(:t3-book-substitution-term-result traversal value typed evidence)`,
with the Traversal as of that call. `replies` is an alist keyed by
`(value typed evidence)`. The value is `(list step traversal evidence)` or
a failure. Supply each reply and call again with the original Traversal and
the accumulated replies. The `:alist` and `:parallel` traversals implement
their own term cases and take `nil` for `replies`.

The prover symbols are `*t3-book-substitution-term*`,
`*t3-book-substitution-list*`, `*t3-book-substitution-sublis*`,
`*t3-book-substitution-sublis-list*`, `*t3-book-substitution-subcor*`,
`*t3-book-substitution-subcor-list*`, `*t3-book-substitution-subcor-var*`,
`*t3-book-substitution-fast-sublis*`, `*t3-book-substitution-fast-sublis-list*`,
`*t3-book-substitution-cons-term*`, `*t3-book-substitution-cons-term1*`,
`*t3-book-substitution-fold-mv*`, `*t3-book-substitution-kwote*`,
`*t3-book-substitution-alist*`, `*t3-book-substitution-vars*`,
`*t3-book-substitution-terms*`, `*t3-book-substitution-strip-cdrs*`, and
`*t3-book-substitution-lookup-term*`. The projection symbol is also available
as `*t3-book-substitution-mv-nth*`.
