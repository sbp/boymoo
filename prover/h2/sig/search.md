# Proof search

Terms, Proofs and Steps use the forms in `prover/sig/proof.md`. A Library uses the form in `prover/sig/library.md`. A Search contains a Library and the configuration used by the search. A `search` argument may also be a Library when no configuration is needed. A `proof` argument may be a Proof, Library or Search.

A Rule has the form `(:h2-rule name pattern action conditions required id)`. Its actions are two-element lists with the strings `"cut"`, `"implies"` or `"conjunct"` first. Conditions are in action order, with conjunctive antecedents visited from left to right. `required` is the set of variables in the pattern and conditions, ordered by their rendering by `h2-search-data-text`. Rule identity distinguishes instances of a fact in different indexes. An `active` list holds Rules in the order in which they were entered, with `nil` for an entry without a rule.

A Context has the form `(:h2-context literals equalities representatives tests contradiction reductions deductions)`. `literals`, `equalities`, `tests`, `reductions` and `deductions` are insertion-ordered alists. The first two map terms to Steps, and `tests` maps each test to `nil`. `representatives` is a set of terms ordered by their printed representation as for Rule variables. `contradiction` is a Step or `nil`. The reduction and deduction tables also mark queries that are in progress. An `opened` argument is the list of function names opened along the current path, including repetitions. A `seen` argument is a set of learned literals, ordered as for Rule variables.

A Search has the form `(:h2-search library opened repeat split-limit rule-heads rewrite-heads hooks replies)`. `opened` and `repeat` are sets of symbols. The two head indexes are insertion-ordered alists from heads to Rules in the order that `configure` visits them. The `nil` key is the bucket for atomic patterns. Bindings are insertion-ordered alists from variables to terms. A pair of a value and an updated Context or bindings is written `(cons value object)`. A failure is the entire result, in the form `(:failure kind message)`.

`h2-search-search-prepare-not-nil` takes a Search and records a Step for
`(not (quote nil))` with the ground dependencies used to construct it.
`h2-search-not-nil-in-proof` takes a Search and a Proof and returns the Step
or failure that `proof-proof-not-nil` would give for that Proof. It can use the
stored result when the dependencies match. `h2-search-search-not-nil` takes
only a Search and uses its Proof.

## Terms and rules

| Function | Arguments in order | Result |
|---|---|---|
| `h2-search-variables` | `term` | Set of unquoted variables in the arguments of the term, ordered as for Rule variables. |
| `h2-search-match` | `pattern`, `term`, `bindings` | `(cons matched-p bindings)`. A failed match retains the bindings installed before the failure. |
| `h2-search-head` | `term` | The head of the compound term or `nil` for an atom. A compound term with a missing field can return a failure. |
| `h2-search-size` | `term` | Size, counting a quotation or atom once and omitting function heads. |
| `h2-search-opposite` | `term` | The argument of a negation or the negation of another term. A compound term with a missing field can return a failure. |
| `h2-search-antecedents` | `term` | List of conjuncts, visiting the test before the true branch and omitting quoted `T`. A compound term with a missing field can return a failure. |
| `h2-search-rule-init` | `name`, `pattern`, `action`, `conditions` | A Rule. |
| `h2-search-rule-from-fact` | `proof`, `name` | Rules in the order visited by the generator. May return a failure a lookup or term error. |
| `h2-search-rule-from-fact-descend` | `formula`, `action`, `conditions`, `name` | The Rules for that formula in the generator's order. May return a failure a term error. |
| `h2-search-rule-apply` | `rule`, `search`, `term`, `context`, `active`, `rewrite` | The first successful instance Step or `nil`, paired with the resulting Context. May return a failure. |

Each of `h2-search-rule-name`, `h2-search-rule-pattern`, `h2-search-rule-action`, `h2-search-rule-conditions`, `h2-search-rule-required`, and `h2-search-rule-id` takes one Rule and returns its named field. `h2-search-rule-with-id` takes a Rule and a replacement identity. A caller that builds additional rule indexes may give their Rules a distinct identity with this function.

## Context and Search

| Function | Arguments in order | Result |
|---|---|---|
| `h2-search-context-init` | None | An empty Context. |
| `h2-search-context-add` | `context`, `proof`, `step` | `(cons added-p context)` with the resulting Context. May return a failure. |
| `h2-search-context-test` | `context`, `term` | The resulting Context with an eligible test retained. May return a failure. |
| `h2-search-search-init` | `library` | An unconfigured Search. |
| `h2-search-search-configure` | `search`, definition names, fact names, repeated definition names, split limit | The configured Search, or a failure from indexing facts. Supply `nil nil nil 80` for the defaults. |
| `h2-search-search-nil-value` | `search`, evidence Step | A Step equating the argument of the proved negation with quoted `NIL`, or a failure. |
| `h2-search-search-deny` | `search`, evidence Step | A Step proving the double negation of the evidence's first literal, or a failure. |
| `h2-search-search-lookup` | `search`, `term`, `context` | An evidence Step, `nil`, or a failure. |
| `h2-search-search-truth` | `search`, `term`, `context`, `active` | A Step for either sign, or `nil`, paired with the resulting Context. May return a failure. |
| `h2-search-search-apply-rules` | `search`, `term`, `context`, `active`, `rewrite` | A Step or `nil`, paired with the resulting Context. May return a failure. |
| `h2-search-search-primitive` | `search`, `term`, `context` | A primitive computation or selector Step, `nil`, or a failure. |
| `h2-search-search-reduce` | `search`, `term`, `context`, `opened`, `active` | The reduction without first registering the normalization query, paired with the resulting Context. May return a failure. |
| `h2-search-search-remove-wrappers` | `search`, `term` | Equality Step for removing lambda applications and `RETURN-LAST`, `nil`, or a failure. |
| `h2-search-search-learn` | `search`, `step`, `context`, `opened`, `seen` | `(cons context seen)` with the resulting Context and set of seen literals, or a failure. |
| `h2-search-search-rewrite-result-in-argument` | `search`, `step`, `index`, `context` | The Step with known equalities applied inside the indexed argument, or a failure. |
| `h2-search-search-rewrite-result-in-argument-rewrite` | `term`, `place`, `inside`, `step`, `search`, `context` | The Step after rewriting the given term and its arguments, or a failure. |
| `h2-search-search-deduce` | `search`, `term`, `context`, `active` | A Step or `nil`, paired with the resulting Context. May return a failure. |
| `h2-search-search-solve` | `search`, `formula`, seed Steps, explicit case terms | The Step for `formula`, or a failure including `unproved` when rewriting and splitting fail. Supply `nil nil` for omitted seeds and cases. |
| `h2-search-search-introduce` | `search`, implication term, conclusion Step | The implication Step, or a failure. |
| `h2-search-search-induction` | `search`, `formula`, `measure`, substitution lists, ordinal Step, case terms | The induction Step, or a failure. Supply `nil` for omitted cases. |
| `h2-search-search-list-induction` | `search`, `formula`, `variable`, additional substitution pairs, `depth` | The list induction Step, or a failure. Supply `nil 1` for the defaults. |

`h2-search-context-literals`, `h2-search-context-equalities`, `h2-search-context-representatives`, `h2-search-context-tests`, `h2-search-context-contradiction`, `h2-search-context-reductions`, and `h2-search-context-deductions` each take a Context and return their named field. `h2-search-context-with-contradiction` takes a Context and a Step or `nil` and returns the Context with that contradiction field.

`h2-search-search-library`, `h2-search-search-opened`, `h2-search-search-repeat`, `h2-search-search-split-limit`, `h2-search-search-rule-heads`, and `h2-search-search-rewrite-heads` each take a Search and return their named field. `h2-search-search-with-library` takes a Search and a Library and returns the Search with its Library replaced. When passed a plain Library in the first argument, it returns the replacement Library. `h2-search-search-with-configuration` takes a Search, the opened set, the repeat set and the split limit. It returns the Search with those three fields replaced.

Pass `nil` for omitted `opened`, `active` and `seen` arguments, and `nil` for the default `rewrite` flag. The constants are `*h2-search-transparent*` and `*h2-search-type-facts*`.

## Inherited calls

`h2-search-search-with-hooks` takes a Search and a list of keywords naming overridden methods. The supported keywords are `:reduce`, `:can-open`, `:lookup`, `:learn`, `:primitive`, and `:apply-rules`. A selected call yields a request of the form `(:h2-search-request :before method args nil)`. `args` are the method's arguments in the order above, excluding the Search. `h2-search-request-p`, `h2-search-request-phase`, `h2-search-request-method`, `h2-search-request-args`, and `h2-search-request-result` take a request and recognize it or return its named field. `h2-search-search-with-replies` takes a Search and the list of replies to requests in the order encountered. To answer a request, append the reply and repeat the initiating call with that reply list.

A reply to `:before` is `:base` to call the base implementation, `:after` to run the base implementation and request a reply to its result, or `(:return result)` to supply the method's result. An `:after` request carries the same operation and arguments and the base result in its last field. Its reply is `(:return result)` or `:base` to retain the base result. Calls from the base implementations still use the overrides. Failures from a base implementation propagate directly.

`h2-search-search-call-with-remainder` takes a Search, an operation keyword, and the operation's argument list after the Search. `:rule-apply` and `:rule-prove-instance` put the Rule first in that list. The keyword names a Search operation such as `:solve`, `:normalize`, or `:list-induction`. A completed call returns `(cons value search)` with the unused replies in that Search. A request or failure is returned in place of the pair. `h2-search-stopped-p` recognizes both forms.

`h2-search-search-call-with-outcome` takes the same arguments as `h2-search-search-call-with-remainder`. It returns `(cons value search)` for both successful values and failures, with the failure in the value position and the unused replies in the Search. A request is the entire result. The caller can handle the failure and continue with the remaining replies.

The `h2-search-search-hooks` and `h2-search-search-replies` accessors return the active hook keywords and the remaining replies of a Search. `h2-search-request` takes a phase, a Search, a method keyword, an argument list, and a base result. It constructs the request with the active Search. A caller can also enable its own method keywords with `h2-search-search-with-hooks` and supply their results through `(:return result)` replies.

`h2-search-object-p` recognizes a Search. `h2-search-set` takes a list of terms and an existing set in textual order. It returns the set with those terms added in the order of the strings returned by `h2-search-data-text`.

## Indexed search

`h2-search-index-find` takes a key and a balanced tree and returns the
matching `(key . value)` pair, or `nil` if absent. `h2-search-index-put`
takes a key, a value and a tree and returns the updated tree. An empty
tree is `nil`. These functions use `equal` for key identity and do not
failure. `h2-search-index-values` takes a tree and a list tail and returns
its values in key order followed by that tail.

`h2-search-search-with-indexes` takes a Search and returns a Search
prepared for indexed search against its current Proof.
`h2-search-search-without-indexes` takes an indexed Search and returns
its ordinary form. `h2-search-search-indexes` takes a Search and returns
its index record, or `nil` for an ordinary Search. An indexed search can
create private Contexts whose reduction and deduction tables use trees.
Literal and test iteration uses the Context's ordered lists.
`h2-search-seen-p` takes a literal
and either form of the learned-literal set and tests membership.

`h2-search-reply-transcript` takes the remaining events and the consumed
events in reverse order and returns a reply transcript. An empty
transcript takes `nil nil`. A transcript is private to one search
invocation. Its events record entry into an unfinished call, the value
of a completed call, or a hook reply. When a hook suspends the invocation,
the request also carries the consumed events. `h2-search-replay-replies`
takes the reply sequence or transcript, the resulting request and its
answer. It extends the reply sequence or constructs a transcript for
resuming the invocation.
