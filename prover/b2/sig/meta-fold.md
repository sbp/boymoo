# Arithmetic folds

An ArithmeticFold has the form `(:b2-arithmetic-fold lib evaluator operation
simple constant operator-name label fold dispatch)`. `lib` is a Library.
`evaluator`, `operation`, and `fold` are symbols in the form given in
`prover/sig/proof.md`. `simple` is a Boolean. `constant` is the quoted identity
of the operation. `operator-name` is the string `"+"` or `"*"`. `label` is the
unqualified evaluator name as a string. `dispatch` maps evaluator tags to
constraint symbols in insertion order, with an existing key retaining its
position when its value changes.

Use the accessors `b2-meta-fold-arithmetic-fold-lib`,
`b2-meta-fold-arithmetic-fold-evaluator`,
`b2-meta-fold-arithmetic-fold-operation`, `b2-meta-fold-arithmetic-fold-simple`,
`b2-meta-fold-arithmetic-fold-constant`,
`b2-meta-fold-arithmetic-fold-operator-name`,
`b2-meta-fold-arithmetic-fold-label`, `b2-meta-fold-arithmetic-fold-fold`, and
`b2-meta-fold-arithmetic-fold-dispatch`. Each takes an ArithmeticFold and
returns the indicated field. `b2-meta-fold-arithmetic-fold-with-lib` takes
an ArithmeticFold and a Library and returns the resulting ArithmeticFold.

The calls below use the prefix `b2-meta-fold-arithmetic-fold-`. `self` is
an ArithmeticFold. A term and a Step use the forms in `prover/sig/proof.md`.
`evidence` is a list of Steps in the supplied order. Pass `nil` for omitted
evidence, and `*b2-bags-a*` for an omitted `env`. A pair `(cons step self)`
contains the ArithmeticFold with the resulting Library, including any
auxiliary definitions and lemmas. Use that Library for subsequent calls.
A failure takes the place of the entire result.

| Function | Arguments in order | Result | Failure |
|---|---|---|---|
| `b2-meta-fold-arithmetic-fold-init` | Library `lib`, evaluator symbol `evaluator`, operator symbol `operation`, Boolean `simple` | ArithmeticFold built from the Library's facts | From reading the evaluator or its constraints |
| `b2-meta-fold-arithmetic-fold-call` | `self`, element list term `elements`, environment term `env` | Fold call | — |
| `b2-meta-fold-arithmetic-fold-ev` | `self`, `term`, environment term `env` | Evaluator call | — |
| `b2-meta-fold-arithmetic-fold-tree` | `self`, element list term `elements` | Call of the selected tree constructor | — |
| `b2-meta-fold-arithmetic-fold-op` | `self`, terms `a`, `b` | Operator call on the two terms | — |
| `b2-meta-fold-arithmetic-fold-install` | `self` | ArithmeticFold whose Library includes the fold definition and its measure | From constructing the definition or measure |
| `b2-meta-fold-arithmetic-fold-fact` | `self`, lemma suffix string `kind`, Step or failure `prove`, binding list `elements` | `(cons step self)` for the specialized lemma | From adding or instantiating the lemma |
| `b2-meta-fold-arithmetic-fold-interpret` | `self`, `term`, evaluator tag `tag`, `evidence` | Equation Step produced from the selected constraint | From lookup or proof construction |
| `b2-meta-fold-arithmetic-fold-rewrite-operands` | `self`, equation Step `equation`, ordered list of Steps or `nil` slots `rules` | Equation Step after rewriting the selected operands | From proof construction |
| `b2-meta-fold-arithmetic-fold-evaluate-arguments` | `self`, equation Step `equation`, ordered list of evaluator tags or `nil` slots `tags`, `evidence` | Equation Step after interpreting the selected operands | From proof construction |
| `b2-meta-fold-arithmetic-fold-identity` | `self`, `term` | Left identity Step | From proof construction |
| `b2-meta-fold-arithmetic-fold-right-identity` | `self`, `term` | Right identity Step | From proof construction |
| `b2-meta-fold-arithmetic-fold-fixed` | `self`, `term`, numeric evidence Step `numeric` | Equation Step for `FIX` of the term | From proof construction |
| `b2-meta-fold-arithmetic-fold-number` | `self`, element list term `elements` | `(cons step self)` for the fold's number type | From proof construction |
| `b2-meta-fold-arithmetic-fold-append-value` | `self`, element list terms `xs`, `ys` | `(cons step self)` for the fold of an append | From proof construction |
| `b2-meta-fold-arithmetic-fold-tree-value` | `self`, element list term `elements` | `(cons step self)` for the evaluation of the tree | From proof construction |
| `b2-meta-fold-arithmetic-fold-fringe-value` | `self`, expression term `expression` | `(cons step self)` for the fold of the fringe | From proof construction |
| `b2-meta-fold-arithmetic-fold-delete-value` | `self`, item term `item`, element list term `elements` | `(cons step self)` for the fold after deleting a member | From proof construction |
| `b2-meta-fold-arithmetic-fold-difference-value` | `self`, element list terms `whole`, `part` | `(cons step self)` for the fold after bag difference | From proof construction |
| `b2-meta-fold-arithmetic-fold-formal-zero` | `self`, element list term `elements` | `(cons step self)` for the formal zero test | From proof construction |

For `fact`, evaluate the proof recipe only when the lemma symbol is absent.
For an existing lemma, pass `nil` for `prove`. The bindings are two-element
lists in the order supplied to `proof-proof-fact`.

The symbol constants are `*b2-meta-fold-bagdiff*`, `*b2-meta-fold-formal-zero*`,
`*b2-meta-fold-tree*`, `*b2-meta-fold-simple-tree*`, and `*b2-meta-fold-u*`.
