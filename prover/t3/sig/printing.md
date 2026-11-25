# Printer count bounds

`lib` is a Library as specified in `prover/sig/library.md`. Terms and Steps
have the forms in `prover/sig/proof.md`. `evidence` is the Evidence object
from `prover/t3/sig/logic.md`. A signed test is `(term holds)`, with `t`
for true and `nil` for false. Tests are in outermost-first order.

| Call | Result | Failure |
|---|---|---|
| `(t3-printing-size-of value)` | The term `(ACL2-COUNT value)`. | None. |
| `(t3-printing-nil-count-bound lib parent evidence)` | A Step bounding the count of quoted `NIL` by the parent's count. | A failure from proof construction. |
| `(t3-printing-nthcdr-tail-bound lib)` | The Library with the suffix-tail bound lemma. | A failure from proof construction. |
| `(t3-printing-take-bound lib)` | The Library with the bounded-prefix lemma. | A failure from proof construction. |
| `(t3-printing-bounded-index lib index length tests)` | A Step proving that the index is at most the length. Pass `nil` for omitted tests. | `unsupported` if the index has no bound rule, or a failure from proof construction. |
| `(t3-printing-taken-head lib term parent)` | A Step bounding the first element of a prefix by the parent's count. | A failure from proof construction. |

`*t3-printing-nthcdr*` and `*t3-printing-take*` are the symbols for
`COMMON-LISP::NTHCDR` and `ACL2::TAKE`. Induction substitutions are
assembled in the order in which the conditional leaves are visited.

`(t3-printing-by-value-next cursor template leaf)` advances a conditional
proof between leaf calls. The cursor carries the Library, term, signed
tests, induction substitutions and pending branches. The macro binds
`lib`, `value`, `tests` and `substitutions` for the leaf form, which
returns `(step lib substitutions)` or a failure. Each branch is visited in
true-branch-first order before its proof is joined to the other branch.
