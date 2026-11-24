# Symbolic application

An Application is `(:l1-application proof function badges definitions kind)`.
`proof` is a Proof, `function` is a quoted prover symbol, `badges` is
an insertion-ordered alist from function symbols to badge lists, and
`definitions` is a set of function symbols represented as a list.
`kind` selects the rules for the base application or a derived application.

The constants are `*l1-application-apply*`,
`*l1-application-apply-primitive*`, `*l1-application-badge*`,
`*l1-application-badge-primitive*` and `*l1-application-evaluator*`.
The last lists the evaluator function symbols. All sets returned by this
book are in the order of their serialized member text.

| Call | Arguments and result | Failure |
|---|---|---|
| `(l1-application-elements term)` | Return the elements of an explicit cons list, or `:none` if the tail is other than quoted NIL. An empty explicit list returns `nil`. | Malformed cons. |
| `(l1-application-consp-cons proof test)` | Return a Step for a `CONSP` test on a cons constructor, or `nil`. | Malformed test or proof construction. |
| `(l1-application-value-functions term)` | Return the set of function names outside quoted code in the translated term. | `UnsupportedApplication` for a lambda head, or a failure from reading a malformed term. |
| `(l1-application-application-init proof function badges extra-definitions definitions)` | Construct an Application from the Proof, the unquoted function symbol, badges and two sets of definition names. Pass `nil` for no extra names and `:default` for the standard evaluator definitions. | None on those arguments. |
| `(l1-application-application-proof application)` | Return the Proof. | None. |
| `(l1-application-application-function application)` | Return the quoted function symbol. | None. |
| `(l1-application-application-badges application)` | Return the badge alist. | None. |
| `(l1-application-application-definitions application)` | Return the definition name set. | None. |
| `(l1-application-application-kind application)` | Return its rule kind. | None. |
| `(l1-application-application-with-kind application kind)` | Return an Application with the same data and kind `:base`, `:lambda` or `:literal`. The kind selects the base rules or the corresponding guarded application override. | None. |
| `(l1-application-application-initial application term)` | Return the first applicable equality Step for the term before unfolding, or `nil`. | Malformed term or proof construction. |
| `(l1-application-application-choose-branch application term)` | Return the equality Step for a selected conditional branch, or `nil`. | Malformed conditional or proof construction. |
| `(l1-application-application-reduce application term)` | Return the reduction equality Step for the term, or `nil`. | Malformed term, proof construction or fuel. |
| `(l1-application-application-arguments application term positions)` | Reduce the term's arguments at the ordered zero-based positions and return the equality Step, or `nil`. | Malformed term, proof construction or fuel. |
| `(l1-application-quoted-application proof function args recursive-badge expected code)` | Return `(quoted-function quoted-lambda left-step right-step)` for the unquoted function symbol and explicit argument-list term. Pass `nil` or `:none` for an absent recursive badge, expected result, or code term. | `UnsupportedApplication`, malformed definition, missing evidence, failed assertion, proof construction or fuel. |
| `(l1-application-select-args args size)` | Return `size` terms projecting successive arguments from the argument-list term. | None for integer `size`. |
| `(l1-application-component data index)` | Return the zero-based projection term from the list term `data`. | An index outside the range from 0 through 2^63 − 1. |
| `(l1-application-select-component proof data index)` | Return the proof reducing the projection at zero-based `index` from the cons-list term. | Malformed data, bad index or proof construction. |

The Proof operations below dispatch on the Proof kind.
In particular, `:l1-warrant` recognizes the warrant constant rules and
uses them in recursive simplification. Evidence is an ordered list of
Steps and definitions is the list of names to unfold. Both default to
`nil`.

| Call | Result | Failure |
|---|---|---|
| `(l1-application-proof-constant proof term)` | The equality Step for a supported constant computation, or `nil`. | Malformed term or proof construction. |
| `(l1-application-proof-simplify proof term evidence definitions)` | The simplification equality Step, or `nil`. | Malformed term, proof construction or fuel. |
| `(l1-application-proof-prove proof term evidence definitions)` | The Step proving the term. | `Unproved` when warrant simplification finds no proof, or a failure from proof construction. |

`l1-application-component` constructs one projection. `l1-application-select-args` constructs the projections for the first `size` arguments.
