# Proof tactics

`lib` is a Library as specified in `prover/sig/library.md`. Use
`library-library-init` to construct it. A term, symbol, and Step have the
forms in `prover/sig/proof.md`.

`(b2-tactics-unproved)` returns the `unproved` failure with an empty
message. `b2-tactics-unproved-p` recognizes it. The constants are
`*b2-tactics-eq*`, `*b2-tactics-eql*`,
`*b2-tactics-atom*`, `*b2-tactics-endp*`, `*b2-tactics-null*`,
`*b2-tactics-symbolp*`, `*b2-tactics-characterp*`, `*b2-tactics-coerce*`,
`*b2-tactics-iff*`, `*b2-tactics-projections*`, `*b2-tactics-logic*`, and
`*b2-tactics-boolean-heads*`. The last three constants are sets used for
membership tests.
Their lists follow serialized symbol order.

| Call | Result and possible failure |
|---|---|
| `(b2-tactics-tag datum name)` | Whether `datum` is a nonempty list with first element `name`, a string. |
| `(b2-tactics-variable term)` | Whether `term` is a symbol datum. |
| `(b2-tactics-cons-parts value)` | A two-element list with the car and cdr of the ground datum `value`. May return a failure on a malformed dot tag. |
| `(b2-tactics-field term index)` | The car after `index` applications of cdr to `term`, with a negative `index` treated as zero. |
| `(b2-tactics-rational-value datum)` | ACL2 rational for an integer or ratio datum, or `nil` for other data. May return a failure on a malformed ratio tag. |
| `(b2-tactics-rational-datum value)` | Integer or ratio datum for an ACL2 rational. |
| `(b2-tactics-match pattern term bindings)` | `(cons matched-p bindings)` with the resulting insertion-ordered variable-to-term table, including bindings made before a failed match. |
| `(b2-tactics-choose lib test evidence prove)` | `(cons step lib)` for the necessary signed cases. The callback argument `prove` is described below. |
| `(b2-tactics-rebuild lib value cons-step)` | Step proving the reconstruction of term `value` from its selectors. May return a failure. |
| `(b2-tactics-first-test term)` | First conditional test in argument traversal order, or `nil` if absent. May return a failure on a malformed conditional. |
| `(b2-tactics-rename-calls term names)` | Term with function positions replaced according to the name-to-name table `names`. May return a failure on a malformed lambda head. |

The functions below use the `b2-tactics-tactics-` prefix. Each may return a failure.
`evidence` is a list of Steps unless a signature says otherwise. `unfold` is
a list of function symbols or exact applications. `rules` is a list of
equality Steps. The default empty lists and `branches` false are `nil`.
`budget` defaults to `1500` and `splits` defaults to `0`.

| Call | Result |
|---|---|
| `(b2-tactics-tactics-linear-form lib term evidence)` | Equality Step after repeated linear cancellation. |
| `(b2-tactics-tactics-exact lib name pattern target)` | The named fact instantiated to match `target` against `pattern`. `name` is a fact name or the string shorthand for a string datum. |
| `(b2-tactics-tactics-use-fact lib name target evidence unfold rules splits branches)` | Step for `target` from the named fact, discharging its side literals and solving its antecedent if it is an implication. Use the actual fact key as `name`. |
| `(b2-tactics-tactics-add-lemma lib name step clause)` | `(cons name-symbol lib)` after adding the lemma. `name` is a string without the `B2-` prefix. Pass `:none` to use the Step's clause, or a list of literals to supply a clause. |
| `(b2-tactics-tactics-close-false lib term evidence)` | Equality Step setting `term` to quoted `NIL`, from the single Step `evidence`. |
| `(b2-tactics-tactics-truth-value lib term value premise)` | Equality Step setting `term` to quoted `T` or `NIL` according to Boolean `value`, or `nil` if no Boolean fact is available. A `nil` premise means to assume the result. |
| `(b2-tactics-tactics-boolean-true lib boolean premise)` | Equality Step setting the first literal of `premise` to quoted `T`, using the Step `boolean` proving its Boolean type. |
| `(b2-tactics-tactics-evidence lib steps)` | Insertion-ordered table of literals to Steps, keeping the first Step for each literal and appending derivations to the pending Steps in derivation order. |
| `(b2-tactics-tactics-constant lib term)` | Equality Step evaluating a ground primitive call, or `nil` if none applies. |
| `(b2-tactics-tactics-normalize lib term evidence unfold rules budget branches)` | Equality Step normalizing `term`, or `nil` if no reduction was made. |
| `(b2-tactics-tactics-prove-ground lib term)` | Step proving a quoted value other than quoted `NIL`. |
| `(b2-tactics-tactics-contradiction lib goal evidence)` | Step for `goal` under the first conflict in the insertion-ordered literal-to-Step table `evidence`, or `nil` if none is found. |
| `(b2-tactics-tactics-from-impossible lib goal premise evidence unfold rules budget branches)` | Step for `goal` by contradiction of the Step `premise`. |
| `(b2-tactics-tactics-solve lib goal evidence unfold rules splits branches)` | Step proving `goal`. |
| `(b2-tactics-tactics-implication lib antecedent consequent prove)` | `(cons step lib)` proving the implication. The callback argument `prove` is described below. |
| `(b2-tactics-tactics-induction-hypothesis lib formula measure bindings smaller)` | Step for the induction hypothesis, using the binding pair list and the ordinality comparison Step `smaller`. |
| `(b2-tactics-tactics-by-induction lib formula variable test smaller bindings base advance advances-when)` | `(cons step lib)` for a one-call induction scheme. `smaller` is the ordinality comparison Step, `bindings` is a list of binding pairs, and `advances-when` defaults to `t`. |
| `(b2-tactics-tactics-on-list lib formula variable base advance extra)` | `(cons step lib)` from induction on a list. `extra` is the list of additional binding pairs. |

Callbacks take and return a Library so their proof-local declarations are
available to subsequent calls. `prove` in `choose` is the list of callback
replies in call order. `prove` in `implication`, and `base` and `advance` in
the induction functions, are single replies. Each reply is `(cons step lib)`.
A missing reply produces `(cons request lib)`, where `request` takes one of
the forms below. Call the callback with the Library and the listed arguments,
then repeat the original call with the reply supplied. Failure from a
callback can be supplied in place of its reply, or in its step position if
the updated Library is needed by the caller.

| Request | Callback arguments after the Library |
|---|---|
| `(:call :choose lib sign evidence)` | Boolean sign and list of evidence Steps. |
| `(:call :implication lib positive)` | Assumption Step for the antecedent. |
| `(:call :advance lib signed hypothesis)` | Assumption Step for the advancing branch and the induction hypothesis Step. |
| `(:call :base lib signed)` | Assumption Step for the base branch. |

The following functions use the B2 linear form. The argument conventions
are in `prover/sig/library.md`.

| Call | Result |
|---|---|
| `(b2-tactics-tactics-linear-equal lib left right integers)` | Step equating `left` and `right`. |
| `(b2-tactics-tactics-less-from-difference lib a b positive-difference integers)` | Step proving `a < b`. |
| `(b2-tactics-tactics-weak-from-difference lib a b nonnegative-difference integers)` | Step proving `a <= b`. |
