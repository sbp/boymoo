# Evaluator witnesses

`functions` is the ordered list of `(function arity)` pairs and `formulas` is the ordered list of `(name formula)` pairs of a constraint statement. Symbols, terms, Steps and entries use the forms in `prover/sig/proof.md`.

The constants are `*b2-evaluator-a*`, `*b2-evaluator-b*`, `*b2-evaluator-assoc*`, `*b2-evaluator-pairlis*`, `*b2-evaluator-kwote*` and `*b2-evaluator-kwotes*`. `b2-tactics-field` constructs a selector from a term and an index.

An Evaluator has the form `(:b2-evaluator library name label ev evl goals operations arity)`. `library` is the Library for proof construction. `name` is the constrained evaluator symbol and `label` is its name string. `ev` and `evl` are the witness symbols. `goals` are the renamed constraint forms in input order. `operations` is the ordered list of `(quoted-operator term)` pairs in the dispatch constraints. `arity` is the maximum argument selector depth. The `b2-evaluator-evaluator-` functions for those field names each take an Evaluator and return the named field.

| ACL2 call | Result | Failure |
|---|---|---|
| `(b2-evaluator-evaluator-equations functions formulas)` | Whether the constraints have the required re-quotation equation. | A failure for a malformed constraint list or term. |
| `(b2-evaluator-evaluator-init library functions formulas)` | Initialized Evaluator. | `unproved` for unsupported constraints or a failure from processing them. |
| `(b2-evaluator-evaluator-dispatch evaluator)` | `(operations arity)` in constraint order. | `unproved` for unsupported dispatch or a failure from processing a constraint. |
| `(b2-evaluator-evaluator-field-count evaluator term)` | Maximum required argument field index, with zero for no field. | `unproved` for unsupported selectors or a failure from a malformed term. |
| `(b2-evaluator-evaluator-install evaluator)` | Evaluator with the definitions and measure entry installed. | Failure from producing or installing the entries. |
| `(b2-evaluator-evaluator-remember evaluator name step)` | `(cons symbol evaluator)` with the named auxiliary lemma installed. `name` is its suffix string. | Failure from adding the lemma. |
| `(b2-evaluator-evaluator-quote-arguments evaluator)` | `(cons symbol evaluator)` for the installed quote-arguments lemma. | Failure from proof construction. |
| `(b2-evaluator-evaluator-projections evaluator)` | `(cons symbols evaluator)` with installed projection lemmas in index order. | Failure from proof construction. |
| `(b2-evaluator-evaluator-quote-invariance evaluator quoted-arguments argument-projections)` | Step for the re-quotation law. The other arguments are the quoted-arguments lemma symbol and the list of projection lemma symbols. | Failure from proof construction. |
| `(b2-evaluator-evaluator-ordinary-constraints evaluator)` | Ordered list of Steps for the remaining constraints. | Failure from proof construction. |
| `(b2-evaluator-evaluator-prove evaluator)` | `(cons entry evaluator)` for the witness and its updated Evaluator. | Failure from proof construction. |
| `(b2-evaluator-noncons library term typed)` | Step deriving the negated cons test on `term` from its symbol Step `typed`. | Failure from proof construction. |
| `(b2-evaluator-witness library functions formulas)` | `(cons entry library)` for the witness and its updated Library. | Failure from initialization or proof construction. |
