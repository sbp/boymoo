# Bags

`lib` is the B2 tactic library. Terms and Steps have the forms in
`prover/sig/proof.md`. Each call can return a failure in place of its result.
A result of the form `(cons step lib)` carries the library after any
lemma additions.

The constants `*b2-bags-a*`, `*b2-bags-u*`, `*b2-bags-v*`,
`*b2-bags-binop*`, `*b2-bags-arg*`, `*b2-bags-term*`, `*b2-bags-del*`,
`*b2-bags-memb*`, `*b2-bags-subbag*`, `*b2-bags-intersect*`,
`*b2-bags-append*`, `*b2-bags-fringe*`, `*b2-bags-occur*`,
`*b2-bags-member-delete*`, `*b2-bags-delete-commutes*`,
`*b2-bags-subbag-delete*`, `*b2-bags-subbag-cdr1*`, `*b2-bags-subbag-cdr2*`,
`*b2-bags-intersect1*`, `*b2-bags-intersect2*`, `*b2-bags-member-append*`,
`*b2-bags-fringe-member*` and `*b2-bags-nonempty-intersection*` are prover
symbols. `*b2-bags-formulas*` is an alist of names to formulas, with entries
in insertion order from `MEMBER-DELETE` through the fringe membership
formula.

| ACL2 call | Arguments and result |
|---|---|
| `(b2-bags-bag-fact lib name bindings)` | A lemma name symbol and an ordered list of `(variable term)` bindings. Returns `(cons step lib)` for the instantiated fact. |
| `(b2-bags-signed lib test)` | A test term. Returns `(list yes no)` with the positive and negative assumption Steps. |
| `(b2-bags-reduced-premise lib premise evidence unfold rules)` | A premise Step, with ordered lists of evidence Steps, unfold terms or names, and rule Steps. Pass `nil` for omitted rules. Returns the possibly reduced premise Step. |
| `(b2-bags-member-delete lib formula)` | The membership after deletion formula. Returns its Step. |
| `(b2-bags-delete-commutes lib formula)` | The commutativity of deletion formula. Returns its Step. |
| `(b2-bags-intersection-cons lib present)` | A positive membership Step for the intersection term. Returns `(cons step lib)` proving the term is a cons. |
| `(b2-bags-append-membership lib formula)` | The append membership formula. Returns its Step. |
| `(b2-bags-prove-bag lib name formula)` | The theorem name symbol and formula. Returns `(cons step lib)` for the proof chosen by the name. |
