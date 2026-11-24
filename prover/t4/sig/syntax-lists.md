# Syntax list proofs

A Library and a Step have the forms specified in `prover/sig/library.md`
and `prover/sig/proof.md`. A term or symbol is a prover datum in the form
specified in `prover/sig/proof.md`. The following constants denote the book's
symbols and recognizer table.

| Constant suffix after `*t4-syntax-lists-` | Value |
|---|---|
| `atom*`, `endp*`, `eq*`, `symbolp*` | The Common Lisp symbols `ATOM`, `ENDP`, `EQ`, `SYMBOLP`. |
| `term*`, `terms*`, `clauses*`, `force*` | The ACL2 symbols `PSEUDO-TERMP`, `PSEUDO-TERM-LISTP`, `PSEUDO-TERM-LIST-LISTP`, `FORCE`. |
| `assoc*`, `and-list*`, `or-list*`, `iff*`, `iff-list*`, `disjoin*`, `disjoin-list*` | The ACL2 symbols `ASSOC-EQUAL`, `AND-LIST`, `OR-LIST`, `IFF`, `IFF-LIST`, `DISJOIN`, `DISJOIN-LST`. |
| `conjoin*`, `conjoin-clauses*`, `clauses-result*`, `flag*` | The ACL2 symbols `CONJOIN`, `CONJOIN-CLAUSES`, `CLAUSES-RESULT`, `T4-LIST-BRANCH`. |
| `list-types*` | An alist from list recognizers to their element recognizers, with `PSEUDO-TERM-LISTP` first. |

A result described as a pair is `(cons value lib)`, with the Library as
it stands on return. Its value can be `nil` when no proof applies, a failure,
or, for a call with replies, a request. An unpaired result can itself
be a failure. Step lists are in the order supplied by the caller. A
binding is a list of two-element lists `(variable replacement)`.

| ACL2 call | Result |
|---|---|
| `(t4-syntax-lists-choose lib equation condition)` | A Step for the equation after selecting the branch by the condition Step. |
| `(t4-syntax-lists-open-body lib call)` | A Step unfolding the call and reducing lambdas at the root of its body. |
| `(t4-syntax-lists-spine lib call shape)` | A pair with the selected base or recursive equation. The shape Step proves or disproves `CONSP` of the object tested in the body. |
| `(t4-syntax-lists-projections lib equation pair)` | A Step for the equation after reducing selectors along the given cons term's spine. |
| `(t4-syntax-lists-constructed-view lib call pair)` | A pair with the equation for the call on a constructed cons term. |
| `(t4-syntax-lists-lift-proof lib step equations)` | The Step after applying the equation Steps in reverse direction, in list order. |
| `(t4-syntax-lists-syntax-type lib call premises)` | A pair with a Step proving the recognizer call. Premises are an alist from terms to Steps in insertion order. |
| `(t4-syntax-lists-recur lib formula obj selector number)` | `(list step binding)`, with the induction hypothesis Step for the given selector on `obj` and the built-in clause number. Defaults are `*library-cdr*` and 3. |
| `(t4-syntax-lists-list-typing lib formula recursive replies)` | A pair with the proof of the typing formula for a recursive list map, or `nil`. |
| `(t4-syntax-lists-evaluate lib call premises replies)` | A pair with the evaluator equation after reducing the projections. Premises are the extra Steps for this equation. |
| `(t4-syntax-lists-binding-evaluation lib formula functions replies)` | A pair with the proof of the binding lookup formula, or `nil`. |
| `(t4-syntax-lists-substitution-evaluation lib formula functions reapplications replies)` | A pair with the proof of the substitution formula, or `nil`. |
| `(t4-syntax-lists-prove-substitution lib name joint term terms eval-before list-before replies)` | A pair with `nil` and the Library containing the joint substitution lemma. The name is an unprefixed string, the joint claim and the four calls are terms. |
| `(t4-syntax-lists-iff-transitive lib first second replies)` | A pair with a Step composing the two equivalence Steps. |
| `(t4-syntax-lists-evaluated-clause-map lib formula recursive functions replies)` | A pair with the proof of the disjoined clause comparison, or `nil`. |
| `(t4-syntax-lists-iff-forward lib equivalence premise)` | A Step applying the forward direction of the given equivalence Step. |
| `(t4-syntax-lists-disjunction lib evaluator list-evaluator clause environment replies)` | A pair with a Step for the disjunction evaluation theorem. The first two arguments after the Library are evaluator symbols. |
| `(t4-syntax-lists-evaluated-clause-result lib formula reapplications replies)` | A pair with the proof of the clause processor formula, or `nil`. |

The `recursive` and `functions` arguments stand for the sets of
recursive definitions and evaluator functions. Their order is immaterial.
`reapplications` is the evaluator rules' insertion-ordered alist with
`((term-evaluator list-evaluator) . (name syntax environment))` entries.

A request has the form `(:call operation arguments)` in the value of a
pair. The caller uses the Library from that pair. `:use-arithmetic`
takes no arguments and returns `nil` with the resulting Library.
`:fact-proof` takes a term and a list of extra Steps for fresh Evidence.
`:evaluator-equation` takes a call and a list of extra Steps for fresh
Evidence. `:evaluator-reapply` takes the evaluator call, list evaluator
symbol, cons Step and distinctness Step. Each lookup returns its Step
or `nil` with the Library. A failure can take the place of the Step.
Start with `replies` equal to `nil`. For each request, append its
`(cons value lib)` reply to `replies` and repeat the original call with
its original Library and other arguments. Requests follow the order of the proof operations.

`(t4-syntax-lists-request-p value)` recognizes a request and does not return a failure. A `:constant` request takes a single term. A `:prove` or
`:simplify` request takes a term, a list of premise Steps and a list of
definition names. Their replies are the resulting Step and Library in
the same pair form. A simplification or constant request can have
`nil` in the Step position.

`(t4-syntax-lists-prove n lib term evidence definitions)` is the
Library-aware inherited `prove` with Ordinals simplification.
`evidence` is a list of Steps. `definitions` is a list of symbols.
Pass `1000000` for `n`. It returns the resulting Step or failure
paired with the Library.

The `t4-syntax-lists-spine-with-replies`,
`t4-syntax-lists-constructed-view-with-replies`, and
`t4-syntax-lists-syntax-type-with-replies` entry points add `replies` as
their final argument and use the ordered `:prove` and `:constant`
requests for BookLogic methods. The forms without replies use the
inherited Ordinals methods. The syntax list theorem recipes use the
BookLogic methods for their calls to these helpers.

The following helpers take the terms, Steps and Library needed at their
point in the proof.

| ACL2 call | Result |
|---|---|
| `(t4-syntax-lists-prove-substitution-hypothesis selector as-term lib obj joint satisfied)` | `(list step binding)` for the selected induction hypothesis. `selector` is a symbol, `as-term` is a Boolean, `obj` and `joint` are terms and `satisfied` is a Step. May return a failure. |
| `(t4-syntax-lists-evaluated-clause-map-transformed spine-shape lib widened left replies)` | The transformed evaluator equation Step from a shape Step and the widening and evaluator terms. |
| `(t4-syntax-lists-evaluated-clause-map-compare-head sign lib old-head after premise replies)` | The equivalence Step for the Boolean sign, the two terms, and the guard Step. |
| `(t4-syntax-lists-evaluated-clause-result-evaluated-parts branch lib opening result processor wanted list-evaluator env replies)` | The ordered component Steps on a selected branch. `branch`, `opening` and `wanted` are Steps, `result`, `processor` and `env` are terms and `list-evaluator` is a symbol. |

The three helpers taking replies return
`(list value lib remaining-replies)`. The value can be a failure or an
ordered request, as in the containing tactic.
