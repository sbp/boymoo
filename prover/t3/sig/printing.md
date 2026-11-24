# Printer count bounds

`lib` is a Library as specified in `prover/sig/library.md`. Terms and Steps
have the forms in `prover/sig/proof.md`. `evidence` is the Evidence object
from `prover/t3/sig/logic.md`. A signed test is `(term holds)`, with `t`
for true and `nil` for false. Tests are in outermost-first order.

| Call | Result | Failure |
|---|---|---|
| `(t3-printing-size-of value)` | The term `(ACL2-COUNT value)`. | None. |
| `(t3-printing-nil-count-bound lib parent evidence)` | A Step bounding the count of quoted `NIL` by the parent's count. | A failure from proof construction. |
| `(t3-printing-index-decrease lib new old evidence)` | A Step for the ordinal decrease of the index count. | `Unsupported` if there is no direct proof, or a failure from proof construction. |
| `(t3-printing-nthcdr-tail-bound lib)` | The Library with the suffix-tail bound lemma. | A failure from proof construction. |
| `(t3-printing-take-bound lib)` | The Library with the bounded-prefix lemma. | A failure from proof construction. |
| `(t3-printing-bounded-index lib index length tests)` | A Step proving that the index is at most the length. Pass `nil` for omitted tests. | `Unsupported` if the index has no bound rule, or a failure from proof construction. |
| `(t3-printing-taken-head lib term parent)` | A Step bounding the first element of a prefix by the parent's count. | A failure from proof construction. |
| `(t3-printing-printing-count lib child parent evidence)` | `(cons step lib)`, with the Step for the transformed child's count bound and the Library with any lemmas added by the selected branch. | `Unsupported` if no branch applies or a transform has an unexpected argument, or a failure from proof construction. |

`*t3-printing-nthcdr*` and `*t3-printing-take*` are the symbols for
`COMMON-LISP::NTHCDR` and `ACL2::TAKE`. Induction substitutions are
assembled in the order in which the conditional leaves are visited.

`(t3-printing-printing-count-with-evidence lib child parent evidence)`
has the same arguments as `t3-printing-printing-count` and returns
`(cons (list step evidence) lib)` with the Evidence after its queries.
`(t3-printing-direct-builtin lib clause evidence)` takes a clause whose
last literal is the desired conclusion and returns `(cons step evidence)`
after trying the built-in clauses in order. Its Step is `nil` if no
built-in clause proves the conclusion. A failure replaces either result.

`(t3-printing-by-value-next cursor template leaf)` advances a conditional
proof between leaf calls. The cursor carries the Library, term, signed
tests, induction substitutions and pending branches. The macro binds
`lib`, `value`, `tests` and `substitutions` for the leaf form, which
returns `(step lib substitutions)` or a failure. Each branch is visited in
true-branch-first order before its proof is joined to the other branch.
