# Structural proof

A Library, a Step and a term have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. Tests are ordered lists of `(term holds)` pairs, with
`t` and `nil` for the two signs. Premises and equations are ordered lists
of Steps. A substitution is a list of two-element `(variable term)` pairs.

An expansion predicate is an ordered list of rules. It accepts a call if
the first matching rule accepts it. With no match it returns false. The
rules are as follows.

| Rule | Match |
| --- | --- |
| `(:term term)` | The whole call equals the term. |
| `(:head operator)` | The call has the given head. |
| `(:arg operator index term)` | The head and the argument at the given index match. Index 1 selects the first argument and index -1 selects the last. |
| `(:constructed operator index)` | The head matches and the argument at the given index is quoted nil or a `CONS` call. |
| `(:reply term answer)` | The whole call equals the term. The rule returns the Boolean or failure in `answer`. |
| `(:any)` | Every call. |

A `Reduction` object has the form
`(:t2-structural-proof-reduction lib expand facts equalities budget)`.
`facts` is a RulerFacts object. `equalities` is a dictionary from left
terms to Steps, in first-insertion order. For repeated left terms, the
last equation whose sides differ supplies the value. The initial search
budget is 24000. Use the constructor and accessors to obtain its fields.
`*t2-structural-proof-aliases*` is the set of alias symbols, ordered by
their printed term representation.

| Function | Arguments in order | Result |
| --- | --- | --- |
| `t2-structural-proof-reduction-init` | Library, expansion predicate, tests, premises, equations | Reduction |
| `t2-structural-proof-reduction-form` | Reduction, term | `(cons step reduction)` for the normal form equality |
| `t2-structural-proof-reduction-normalize` | Reduction, term, RulerFacts context, integer depth, list of already opened terms and operators | `(cons (list step context) reduction)` with the optional equality and the resulting context and Reduction |
| `t2-structural-proof-reduction-can-open` | Reduction, term, list of already opened terms and operators | Boolean for whether to unfold the term |
| `t2-structural-proof-reduction-replacement` | Reduction, term, RulerFacts context, integer depth, list of already opened terms and operators | `(cons (list step context) reduction)` with the optional equality and the resulting context and Reduction |
| `t2-structural-proof-reduce` | Library, expansion predicate, tests, premises, equations, term | `(cons step lib)` for a freshly initialized Reduction's normal form equality |
| `t2-structural-proof-congruence` | Library, first and second terms | Equality Step or `nil` |
| `t2-structural-proof-solve` | Library, goal term, expansion predicate, tests, premises, equations, integer depth | `(cons step lib)`. Pass the search's depth bound as an integer. |
| `t2-structural-proof-smaller` | Library, formula term, root term, child term, tests, extra Steps, additional substitution | Two-element list of the induction Step and the substitution |
| `t2-structural-proof-induction-instance` | Library, formula term, descent Step, substitution | Instantiated induction Step |
| `t2-structural-proof-components` | Library, premise Step, tests, component count, known Steps | `(cons steps lib)`, with the component Steps in predicate order |
| `t2-structural-proof-induct` | Library, formula term, root term, case Step, list of substitutions | Induction Step |

Each call in the table can return a failure in place of its result. A
`step` inside a normalization or replacement result can be `nil`. The
`lib` and `reduction` in paired results include any added lemmas. Calls
with an optional list argument take `nil` for an empty list.

The accessors `t2-structural-proof-reduction-lib`,
`t2-structural-proof-reduction-expand`, `t2-structural-proof-reduction-facts`,
`t2-structural-proof-reduction-equalities` and
`t2-structural-proof-reduction-budget` take a Reduction and return the
corresponding field. They cannot fail.

`(t2-structural-proof-reduction-make lib expand facts equalities budget)`
constructs a Reduction from its five fields and cannot fail.
