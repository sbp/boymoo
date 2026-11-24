# Function equality and caller congruence

`p` is a Library as specified in `prover/sig/library.md`. Terms and Steps
have the forms in `prover/sig/proof.md`. Evidence and bindings are lists
in argument order. All proof operations below may return a failure.

| ACL2 call | Arguments and result |
|---|---|
| `(h4-function-equality-apply-at p equivalence arguments)` | Step instantiating an extensional equivalence Step at the argument-list term. |
| `(h4-function-equality-apply-equivalence p left right checked)` | Extensional equivalence Step from the Step `checked` at the witness of functions `left` and `right`. |
| `(h4-function-equality-unequal-functions p equivalence unequal)` | Three-element list of the left tame Step, right tame Step and extensional equivalence Step under the two supplied premises. |
| `(h4-function-equality-introduce-fn-equal p left right evidence)` | Step establishing `FN-EQUAL` for functions `left` and `right` with the evidence Steps. |
| `(h4-function-equality-pointwise-lemma p)` | `(cons name p)` with the local lemma's name symbol and the updated Library. |
| `(h4-function-equality-fn-equal-is-equivalence p formula)` | Step proving the Boolean, reflexive, symmetric and transitive properties in `formula`. |
| `(h4-function-equality-loop-congruence p formula)` | `(cons step p)` with the congruence Step and the resulting Library. |

The constants have prefix `*h4-function-equality-` and suffix `*`.
Their names are `apply`, `apply-equivalence`, `apply-witness`,
`apply-definition`, `apply-necessity`, `booleanp`, `fn-equal`,
`fn1`, `fn2` and `args`.

## CallerCongruence

A CallerCongruence is `(:h4-function-equality-caller-congruence p formula
measure descent premise left-function right-function call substitutions
pointwise)`. Use its constructor and accessors. `substitutions` holds
the collected ordered binding lists, and `pointwise` is the local
lemma name or `nil` before it is built.

| ACL2 call | Arguments and result |
|---|---|
| `(h4-function-equality-caller-congruence-init p formula measure descent)` | CallerCongruence for the formula and measure. Pass `nil` for an absent measure. |
| `(h4-function-equality-caller-congruence-p caller)` | The current Library. |
| `(h4-function-equality-caller-congruence-application caller left right evidence)` | `(cons step caller)` with the application Step and updated CallerCongruence. |
| `(h4-function-equality-caller-congruence-conditional caller left right evidence)` | `(cons step caller)` with the conditional Step and updated CallerCongruence. |
| `(h4-function-equality-caller-congruence-compare caller left right evidence)` | `(cons step caller)` with the comparison Step and updated CallerCongruence. Pass `nil` for omitted evidence. |
| `(h4-function-equality-caller-congruence-prove caller ordinal)` | `(cons step caller)` with the congruence Step and updated CallerCongruence. Pass `nil` for an absent ordinality Step. |

Use `:selector` as `descent` for selector decreases, or `nil` when no
descent can be requested. For a caller-supplied descent function, pass
`(:callback replies)`. The replies are an ordered alist of
`((comparison evidence) . result)` entries. A result is a failure or
`(cons step p)` with the Library after that descent. An unanswered
request is `(:h4-function-equality-descent-request comparison evidence
p)`. Evaluate the callback on the requested comparison and evidence
using the supplied Library, add its reply, and start the call again
from the initial CallerCongruence with the enlarged reply alist.

`h4-function-equality-descent-request-p` recognizes a descent request.
CallerCongruence accessors share the prefix
`h4-function-equality-caller-congruence-`. Their suffixes are
`p`, `formula`, `measure`, `descent`, `premise`, `left-function`,
`right-function`, `call`, `substitutions`, and `pointwise`. Each takes
the CallerCongruence and returns the named field.

`(h4-function-equality-build p)` returns the Library with the inherited
arithmetic support built in declaration order. It uses the H4 implication,
conjunction and constant rules and can return a failure.
