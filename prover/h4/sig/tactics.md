# Proof-producing normalization and propositional reasoning

A Tactics object uses the Library representation in `prover/sig/library.md`. A named `p` argument is that Library. For inherited Proof methods pass `(library-library-proof p)`. Terms and Steps have the forms given in `prover/sig/proof.md`. An evidence list or a list of rewrite Steps is in the supplied order. Definition names are a list of symbols.

| Call | Result |
|---|---|
| `(h4-tactics-car-data value)` | The first element of the unquoted datum `value`, or the NIL datum. |
| `(h4-tactics-cdr-data value)` | The tail datum, using a dotted pair's tail where applicable, or the NIL datum. |
| `(h4-tactics-match-term pattern term bindings)` | `(cons matched-p bindings)` with the resulting dictionary. Bindings are in insertion order, including bindings made before an unsuccessful match. |
| `(h4-tactics-tactics-add-statement p kind fields)` | The Library with the statements admitted as facts and definitions. `kind` is a string and `fields` is the ordered list of parsed fields. |
| `(h4-tactics-tactics-local-lemma p label step)` | `(cons name library)` with the appended entry and fact. `label` is a string or symbol. |
| `(h4-tactics-tactics-fact-instance p term evidence names rewrite)` | The first matching and applicable fact Step, or `nil`. Pass `:none` to examine all facts in insertion order, or a list of names in search order. `rewrite` is Boolean. |
| `(h4-tactics-tactics-constant p term)` | A Step for the constant computation of `term`, or `nil`. |
| `(h4-tactics-tactics-case-of p formula test yes no)` | The joined Step. `yes` and `no` are the results of proving `formula` with the true and false assumptions, respectively. The positive proof is obtained first. |
| `(h4-tactics-tactics-propositional-lemmas p)` | The Library with the five propositional entries appended in order. |
| `(h4-tactics-tactics-imply p formula conclusion)` | A Step proving the implication `formula` from the `conclusion` Step. |
| `(h4-tactics-tactics-modus-ponens p step evidence)` | A Step proving the conclusion of the implication Step from the premise Step. |
| `(h4-tactics-tactics-conjunct p step)` | The list of the two Steps extracted from the conjunction Step, in conjunct order. |
| `(h4-tactics-tactics-conjunction p formula first second)` | A Step proving the conjunction `formula` from the first and second conjunct Steps. |
| `(h4-tactics-tactics-guarded p test conclusion holds)` | A Step placing the `conclusion` Step in the selected branch of `test`. `holds` defaults to `t`. |
| `(h4-tactics-tactics-nil-value p negative)` | An equality Step for the NIL value of the negated term proved by `negative`. |
| `(h4-tactics-tactics-non-nil p equality)` | A Step proving the truth of the left side of `equality` when its right side is a quoted non-NIL datum. |
| `(h4-tactics-tactics-from-contrapositive p step evidence)` | A Step using the contrapositive implication Step and the positive evidence Step. |
| `(h4-tactics-tactics-select-literal p term)` | A Step selecting the branch of an IF term whose test is a literal. |
| `(h4-tactics-tactics-rewrite-context p term expand initial)` | An equality Step rewriting redexes in `term`. `expand` is `:none` to open only lambdas and return-last wrappers, or the list of names to expand in closed evaluation. `initial` is a Step or `nil`. |
| `(h4-tactics-tactics-evaluate-closed p term expand)` | The equality Step for closed evaluation with the given list of definitions. |
| `(h4-tactics-tactics-normalize p term evidence expand rewrites provide)` | The equality Step for normalization. `expand` is the list of definition names. `provide` is described below. |
| `(h4-tactics-tactics-establish p formula evidence expand rewrites provide)` | A Step proving `formula` through normalization. `provide` is described below. |

Each call can return a failure as its entire result, except `h4-tactics-car-data`. For optional lists pass `nil`. `initial` defaults to `nil`, and `rewrite-context` defaults to `:none` for `expand`. `fact-instance` defaults to `:none` for `names` and `nil` for `rewrite`. If an application supplies a failure in place of either branch Step to `case-of`, that failure is the result, with the positive branch checked first.

For normalization or establishment without a provider, pass `nil`. A provider that already has its replies is an association list with `(term . result)` entries, where `result` is a Step, `nil`, or a failure. Its entries are in query order and an absent term gives `nil`. For on-demand evaluation, pass `(:h4-tactics-provider . replies)`. An absent term then produces `(:h4-tactics-request term)` as the entire result. Compute its reply, add it to `replies`, and call again with the same other arguments. An entry with a `nil` result records that the provider returns no reduction for that term. `h4-tactics-request-p` and `h4-tactics-request-term` take the returned object and give the request test and the requested term. `h4-tactics-constructor-provider` takes the constructor equality Step and builds the provider for CAR, CDR, and CONSP of a CONS expression.

The book's constants are `*h4-tactics-return-last*`, `*h4-tactics-symbolp*`, `*h4-tactics-symbol-name*`, `*h4-tactics-coerce*`, `*h4-tactics-implies-elimination*`, `*h4-tactics-implies-conclusion*`, `*h4-tactics-implies-false-premise*`, `*h4-tactics-first-conjunct*` and `*h4-tactics-second-conjunct*`.

For a provider with observable updates, pass `(:h4-tactics-ordered-provider . replies)`. Here `replies` is the list of reply values in call order, including `nil` replies and separate replies for repeated requests of the same redex. Callers thread their own provider state between requests. This form retains the results of previous visits within one normalization, so reusing the result of a visit consumes no reply. An exhausted reply list produces the same `(:h4-tactics-request term)` as the association-list form. Append the next reply and call again with the same other arguments.
