# Measures that decrease

`prover/descent.lisp` proves the obligations of termination (`prover/sig/termination.md`) for the measures that the shared Library knows: the size `ACL2-COUNT` under `CAR` and `CDR`, the gap to a bound, a size with one added, and a sum of lengths. Each proof is a recipe that asks for the tests that rule the recursive call. Terms and Steps have the forms of `prover/sig/proof.md`, and `lib` is a Library (`prover/sig/library.md`). A failure (`prover/FAILURES.md`) is the whole value of a function that returns one.

## Hypotheses

A Hypotheses is `(:hypotheses proof tests extra found)`.

- `proof` is a Library or a Proof.
- `tests` is a list of signed tests `(term holds)`, those that rule the call.
- `extra` is a table (`prover/sig/basics.md`) from terms to the Steps that the caller gave, each under its first literal.
- `found` is a table from terms to the Steps that queries have made so far.

A query returns `(cons step hypotheses)`: the Step, or `nil` when there is none, and the Hypotheses with what was found added. The caller goes on with the Hypotheses returned.

| Call | Value | Failure |
|---|---|---|
| `(descent-hypotheses-init proof tests extra-steps)` | The Hypotheses of the Library or Proof, the tests and the list of Steps, with nothing found. | `"index"` for a Step with an empty clause. |
| `(descent-hypotheses-proof hypotheses)` | The Library or Proof. | |
| `(descent-hypotheses-tests hypotheses)` | The signed tests. | |
| `(descent-hypotheses-extra hypotheses)` | The table of the Steps given. | |
| `(descent-hypotheses-found hypotheses)` | The table of the Steps found. | |
| `(descent-hypotheses-with-found hypotheses found)` | The Hypotheses with the given table of Steps found. | |
| `(descent-hypotheses-with-proof hypotheses proof)` | The Hypotheses with the given Library or Proof, and the same tests and tables. | |
| `(descent-hypotheses-remember hypotheses term step)` | The Hypotheses with the Step found for the term. | |
| `(descent-hypotheses-put-new hypotheses term step)` | The same, unless a Step has been found for the term already. | |
| `(descent-hypotheses-find hypotheses term)` | The pair of a Step of `term` and the Hypotheses. The Step is the one given or found for the term; or the assumption of a test that is the term, signed `t`, or whose negation is the term, signed `nil`; or a conjunct of a test signed `t` that has the form `(IF a (IF b c 'NIL) 'NIL)`, the conjuncts that are split off on the way being found as well. `nil` for the Step when no test gives the term. | Those of the rules. |
| `(descent-hypotheses-require hypotheses term)` | The same pair. | `"value"`, with the message `Missing hypothesis` and the text of the term, when there is no Step. |
| `(descent-missing-hypothesis term)` | That failure. | |
| `(descent-proof object)` | The Proof of a Library, and a Proof itself. | |
| `(descent-conjuncts term prefix)` | `(conjuncts . last)` for a term of the form `(IF a (IF b c 'NIL) 'NIL)`: the list of `a`, `b` and so on after the members of `prefix` reversed, and the last term `c`. The caller passes `nil` for `prefix`. | `"index"`. |

## The recipes

A goal is the literal `(O< smaller measure)` that an obligation ends in. Each recipe returns `(cons step hypotheses)`, a Step of the goal with the Hypotheses that result. Where a recipe adds a lemma of its own to the Library and the Hypotheses held that Library, the Hypotheses returned hold the new one.

| Call | The goal and the value | Failure |
|---|---|---|
| `(descent-direct-builtin lib clause hypotheses)` | For a clause whose last literal is the goal: an instance of one of the facts `"built-in-clause-1"` to `"built-in-clause-23"` whose first literal is the goal. An instance whose literals are all in `clause` is returned as it is. Otherwise, when `hypotheses` is not `nil`, the first instance whose other side literals the Hypotheses settle, with those discharged. The Step is `nil` when there is none. | `"index"` for an empty clause. |
| `(descent-measure-ordinal lib measure)` | A Step of `(O-P measure)`, not a pair: by a built-in clause, by `GAP-ORDINAL` for a call of `SELF-GAP`, and otherwise from `(NATP measure)` by `NATURAL-ORDINAL`. | Those of `descent-library-natural`. |
| `(descent-selector-chain lib child parent hypotheses)` | A Step of `(< (ACL2-COUNT child) (ACL2-COUNT parent))`, where `child` is `CAR`s and `CDR`s applied to `parent`. Each selector's argument is asked for as `(CONSP argument)`; where the Hypotheses have it the step is strict, by a built-in clause, and where not it is weak, by `COUNT-CAR-WEAK` or `COUNT-CDR-WEAK`. | `"value"`, with the message `Expected a selector path from` and the text of `parent`, when `child` is not so made. `"assertion"` when no step is strict. |
| `(descent-selector-decrease lib goal hypotheses)` | The goal `(O< (ACL2-COUNT child) (ACL2-COUNT parent))`, `child` being `CAR`s and `CDR`s applied to `parent`, also inside `RETURN-LAST`. A single selector needs `(CONSP parent)` among the Hypotheses. | `"assertion"` when the goal is not of two sizes. `"value"` for a missing hypothesis. Those of `descent-selector-chain`. |
| `(descent-gap-decrease lib goal hypotheses)` | The goal `(O< (SELF-GAP bound new) (SELF-GAP bound old))`, by `GAP-DECREASE`, in two cases. When `bound` is a constant, `new` is `(BINARY-+ '1 old)`, and the Hypotheses give `(NATP old)` and `(< old bound)`. Otherwise `bound` is `(BINARY-+ '1 n)`, `new` is `(BINARY-* '10 old)`, and the Hypotheses give `(INTEGERP n)`, `(INTEGERP old)`, `(< '0 old)` and `(NOT (< n old))`. | `"assertion"` when the two bounds differ. `"value"` for a missing hypothesis. |
| `(descent-walk-decrease lib goal hypotheses)` | The goal `(O< smaller measure)` where each of the two is a size `(ACL2-COUNT x)` or a size with one added, `(BINARY-+ '1 (ACL2-COUNT x))`. Either the argument of the smaller size is `CAR`s and `CDR`s applied to that of the other, or the two sizes are the same and only `measure` has one added. | `"assertion"` when only `smaller` has one added, and when the sizes are the same and the one added does not decide. Those of `descent-selector-chain`. |
| `(descent-run-decrease lib goal hypotheses)` | The goal `(O< smaller measure)` where the two are sums of two terms that differ in one of them, which is `(LEN x)` in `measure` and `(LEN (CDR x))` in `smaller`. The Hypotheses give `(CONSP x)`. By `LEN-CDR-LESS` and `LESS-SHIFT`. | `"assertion"` when the sums are not so. `"value"` for a missing hypothesis. |
| `(descent-shift lib step offset left-offset)` | From a Step of `(< a b)`, a Step of `(< (BINARY-+ a offset) (BINARY-+ b offset))`, or of `(< (BINARY-+ offset a) (BINARY-+ offset b))` when `left-offset` is `t`. Not a pair. | That of the integer type of `a`, `b` or `offset`. |

## Types that add lemmas

For a Library of the kind `:base` these are `library-library-natural` and `library-library-type-of` with the Library unchanged. For the kinds `:slice` and `:book` they also prove the type of a call of `NFIX` or `MIN`, when the Proof has the definition, and of `LENGTH`, and of a sum, a product or a negation over such terms; the first need of each adds a lemma to the Library, `LIBRARY-NFIX`, `MINIMUM-NATURAL` or `LENGTH-NATURAL`. Each returns `(cons step library)` with the Library that has the lemmas.

| Call | Value | Failure |
|---|---|---|
| `(descent-library-natural lib term)` | The pair of a Step of `(NATP term)` and the Library. | `"Fuel"`, named `descent-library-natural`. Those of `library-library-natural`. |
| `(descent-library-type-of lib term evidence)` | The pair of a Step of `(INTEGERP term)` and the Library. `evidence` is a list of Steps. | Those of `library-library-type-of`. |
| `(descent-measure-ordinal-with-library lib measure)` | The pair of the Step of `descent-measure-ordinal` and the Library. | |
| `(descent-shift-with-library lib step offset left-offset)` | The pair of the Step of `descent-shift` and the Library. | |

## Recipes that ask

A caller that keeps hypotheses of another form, as `prover/rulers.lisp` does, runs a recipe through

```
(descent-query-recipe recipe lib arguments hypotheses replies)
```

`recipe` is `:direct-builtin`, `:selector-chain`, `:selector-decrease`, `:gap-decrease`, `:walk-decrease` or `:run-decrease`, and `arguments` is the list of the recipe's arguments between `lib` and `hypotheses`. `replies` is a table from terms to `(step . remember)`, the answers that the caller has given so far: `step` is a Step or `nil`, and when `remember` is not `nil` the Step is put among those found.

The value is the recipe's pair, or a failure, or a request `(:descent-request term hypotheses)`: the recipe needs `term`, the Hypotheses do not give it, and `replies` has no entry for it. The caller finds its answer, adds it to `replies`, and calls again with the same arguments. Any other `recipe` gives the failure `"value"`.

| Call | Value |
|---|---|
| `(descent-request-p value)` | Whether the value is a request. |
| `(descent-request-term request)` | The term asked for. |
| `(descent-request-hypotheses request)` | The Hypotheses at the time of asking. |

`(descent-let* ((name form) ...) body)` is a macro. It binds each name in order to the value of its form, and returns the first value that is a failure or a request. When none is, it returns the value of `body`.

## Parts that other books call

| Call | Value |
|---|---|
| `(descent-match-argument pattern term bindings)` | `(cons matched bindings)`: whether `term` is `pattern` with one term in the place of the variable `X` throughout, and the table `bindings` with that term put for `X`. |
| `(descent-builtin-matches indices proof clause goal matches)` | For the built-in clauses of the numbers in the list `indices` whose first literal fits `goal`: `(step)` for the first instance whose literals are all in `clause`, and otherwise `(nil . instances)` with the instances in order. The caller passes `nil` for `matches`. |
| `(descent-selector-chain-edges child parent edges)` | The list of `(selector argument)` for the selectors between `parent` and `child`, the one applied to `parent` first. `nil` when `child` is `parent` or is not so made. The caller passes `nil` for `edges`. |
| `(descent-selector-edge lib selector argument evidence)` | A Step that compares `(ACL2-COUNT (selector argument))` with `(ACL2-COUNT argument)`: strict when `evidence` is a Step of `(CONSP argument)`, and weak when it is `nil`. |
| `(descent-selector-step lib actual parent hypotheses replies)` | The pair of a Step of `(O< (ACL2-COUNT actual) parent)` and the Hypotheses, for `parent` of the form `(ACL2-COUNT base)`. `replies` is as in `descent-query-recipe`, or `:plain` for none. |
| `(descent-shift-left lib step a b offset)` | From a Step of `(< (BINARY-+ a offset) (BINARY-+ b offset))`, the Step with `offset` on the left of both sums. |
