# Evaluator projection transformers

Terms and Steps use the forms in `prover/sig/proof.md`. `lib` is a Library
in the form in `prover/sig/library.md`. Evidence uses the representation in
`prover/t4/sig/structural.md`. The constants `*t4-mvmeta-transform*`,
`*t4-mvmeta-transform-step*` and `*t4-mvmeta-transform-correct*` are the
symbols for `MV-NTH-EVAL-FN`, `MV-NTH-EVAL-REC` and
`EVAL-FOR-MV-NTH-REC-THM`.

| ACL2 call | Result |
|---|---|
| `(t4-mvmeta-choose lib equation premise)` | A Step chaining the equality Step `equation` to the selection of its right-side conditional under Step `premise`. May return a failure. |
| `(t4-mvmeta-index-selector lib term shape index-test)` | A Step for the selected branch of the index application `term`. `shape` is its list's shape Step and `index-test` is the Step about whether its index is zero. May return a failure. |
| `(t4-mvmeta-index-equivalence lib index value)` | `(cons step lib)` for equivalence of `NTH` and `MV-NTH` applied to terms `index` and `value`, with the added equivalence lemma if needed. The step position can hold a failure. |
| `(t4-mvmeta-evaluate lib call evidence replies)` | `(cons (list step evidence) lib)` for an evaluator `call` term, with updated Evidence and Library. The step position can hold a failure or a request. |
| `(t4-mvmeta-recursive-transformer lib formula)` | `(cons step lib)` for the correctness of the recursive projection transformer, or `nil` in the step position for an unmatched formula term. The step position can hold a failure or a request. |
| `(t4-mvmeta-projection-transformer lib formula)` | `(cons step lib)` for the correctness of the public projection transformer, or `nil` in the step position for an unmatched formula term. The step position can hold a failure or a request. |

The two transformer calls also have `-with-replies` entry points that take
`lib`, `formula`, and `replies`. Each two-argument call starts with empty
replies. A request has the form `(:call kind lib . args)`. For `:arithmetic`
there are no additional arguments and the reply is `(cons nil lib)` with
arithmetic initialized. For `:evaluate` the arguments are an evaluator call
term and Evidence, and for `:known` they are a requested term and Evidence.
Both replies have the form `(cons (list step evidence) lib)` with the state
after the call, with an optional Step or a failure in the step position.
On receiving a request, add `(request . reply)` to the reply alist and
repeat the original call. The requests follow the order of the proof operations.

`(t4-mvmeta-index-selector-with-library lib term shape index-test)` returns
`(cons step lib)` and retains any lemmas added during the proof of the
index test. The step position can hold a failure. The two internal branch
visitors use this result.

`(t4-mvmeta-request-p value)` recognizes a request and does not return a failure.

The BookLogic forms `t4-mvmeta-index-selector-with-replies` and
`t4-mvmeta-index-equivalence-with-replies` take the same arguments as
`t4-mvmeta-index-selector-with-library` and `t4-mvmeta-index-equivalence`,
respectively, followed by the reply alist. They return `(cons step lib)`
and can put a failure or a request in the step position. Pass `:ordinals`
for the inherited Ordinals proof operation in these two index recipes.

The transformers and these index recipes can request `:prove` with a
term, a list of premise Steps and a list of definitions to unfold, in
that order. The reply is `(cons step lib)` from BookLogic's proof
operation, with a failure allowed in the step position.
