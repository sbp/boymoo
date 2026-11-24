# Recipes

A Recipes object has the form `(:h2-recipes search names)`. `search` is the
inherited Search object described in `prover/h2/sig/search.md`. `names` is an
association list from the ASCII name strings of definitions to prover symbols,
in definition insertion order. A definition with the same name string replaces
the value without moving the key.

| Function | Arguments and result | Failure |
|---|---|---|
| `(h2-recipes-make-recipes search names)` | Construct a Recipes object from its Search and name map. | None |
| `(h2-recipes-recipes-search recipes)` | Return the inherited Search. | None |
| `(h2-recipes-recipes-names recipes)` | Return the name map. | None |
| `(h2-recipes-recipes-with-search recipes search)` | Replace the inherited Search, retaining the name map. | None |
| `(h2-recipes-recipes-with-names recipes names)` | Replace the name map, retaining the inherited Search. | None |

The tables use `recipes` for the object above and `formula` for a prover term.
`entry` is a Library entry as in `prover/sig/library.md`. `kind` is a statement
word string and `data` is its list of parsed, frozen arguments.

In the recipe methods, `definitions` and `repeat` are whitespace-separated
strings of definition names. Each defaults to `""`. `facts` is a list of rule
names, `seeds` a list of Steps, `cases` a list of tests, and `updated` a list
of two-element binding lists. These four lists default to `nil`. `variable`
is a name string and defaults to `nil` in `derive` and `auxiliary`. `depth`
defaults to `1` and `split-limit` to `80`. All arguments are explicit in ACL2.

A call that produces a value and updates the Recipes returns
`(cons value recipes)` with the resulting Recipes. A missing proof is `nil`
in the value position. A failure is the whole result.

| Function | Arguments and result | Failure |
|---|---|---|
| `(h2-recipes-calls-state-read term)` | Test whether `term` calls a state reader outside a quotation. | None on prover terms |
| `(h2-recipes-recipes-init)` | Initialize the ground Recipes, build its library, and add the two recipe lemmas. | A failure from proof construction |
| `(h2-recipes-recipes-admit recipes kind data)` | Return the Recipes after recording the definitions, facts or constraints in the statement. | A failure from reading the statement or adding a definition |
| `(h2-recipes-recipes-dependencies recipes entry)` | Return the needed auxiliary entries in Library order, followed by `entry`. | A failure from writing an entry name |
| `(h2-recipes-recipes-double-cdr-lemma recipes)` | Return the Recipes with the strict count bound for two `CDR` calls. | A failure from proof construction |
| `(h2-recipes-recipes-successor-bound recipes)` | Return the Recipes with the integer successor bound. | A failure from proof construction |
| `(h2-recipes-recipes-set-rules recipes definitions facts repeat split-limit)` | Return the configured Recipes. | Failure for missing names or unusable configuration. |
| `(h2-recipes-recipes-derive recipes formula definitions facts variable depth repeat seeds cases split-limit)` | Return the Step for `formula`, by list induction when `variable` is supplied, with the configured Recipes. | A failure from configuration or proof search |
| `(h2-recipes-recipes-auxiliary recipes name formula definitions facts variable depth repeat seeds cases split-limit)` | Return the prefixed fact name string with the Recipes containing that fact. | A failure from configuration, proof search or adding the lemma |
| `(h2-recipes-recipes-true-list-facts recipes)` | Return the two fact name strings for `CONS` and `CDR`, in that order, with the resulting Recipes. | A failure from proof construction |
| `(h2-recipes-recipes-index-induction recipes formula variable definitions facts updated cases)` | Return the index induction Step with the configured Recipes. | A failure from configuration or proof search |
| `(h2-recipes-recipes-oracle-update-fact recipes)` | Return the oracle update fact name string with the Recipes containing that fact. | A failure from proof construction |
| `(h2-recipes-recipes-nth-index-fact recipes)` | Return the NTH index equality fact name string with the Recipes containing that fact. | A failure from proof construction |
| `(h2-recipes-recipes-length-update recipes formula)` | Return the length update Step with the resulting Recipes. | A failure from reading the formula or proof construction |
| `(h2-recipes-recipes-nth-update recipes formula)` | Return the NTH update Step with the resulting Recipes. | A failure from reading the formula or proof construction |
| `(h2-recipes-recipes-read-state recipes formula)` | Return the state read Step with the resulting Recipes. | A failure from reading the formula or proof construction, or `Fuel` |
| `(h2-recipes-recipes-symbol-equality recipes formula)` | Return the symbol equality Step with the resulting Recipes. | A failure from reading the formula or proof construction |
| `(h2-recipes-recipes-prove-shape recipes formula)` | Return a Step selected by formula shape or `nil`, with the resulting Recipes. | A failure from reading the formula or proof construction |
| `(h2-recipes-recipes-prove-theorem recipes theorem formula)` | Return a Step selected by formula shape or theorem name string, or `nil`, with the resulting Recipes. | A failure from reading the formula or proof construction |

`*h2-recipes-countdown*` lists the index countdown rule names in declaration order. `*h2-recipes-state-fields*` is the string of state field names.
`*h2-recipes-list-proofs*` and `*h2-recipes-direct-proofs*` are association
lists keyed by theorem name, in declaration order.

`h2-recipes-index-lemmas` and `h2-recipes-maximum-lemmas` each take a
Recipes and return the Recipes after discharging the arithmetic book's
derivation requests, or a failure. Recipes that invoke Search can also
return a Search method request when used with an inherited method hook.

| Helper | Arguments and result | Failure |
|---|---|---|
| `(h2-recipes-call-search recipes method arguments)` | Call the Search operation named by the keyword `method`, with its ordered argument list excluding the Search. Return `(cons value recipes)` with the unused Search replies in the resulting Recipes. | A search failure or an inherited method request |
| `(h2-recipes-lemma recipes name claim step conditions)` | Add a lemma with an unprefixed name string, claim term, proof Step and ordered list of side literals. Return the Recipes containing the lemma. | A failure from adding the lemma |

`(h2-recipes-with-results ((name form) ...) result)` evaluates its bindings
in order. It returns the first failure or inherited Search request that it
encounters, or evaluates `result` with the completed bindings.
