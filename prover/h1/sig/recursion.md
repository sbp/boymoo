# Induction from recursive calls

`proof` is the H1 Prover from `tactics`. Terms and Steps have the forms
given in `prover/sig/proof.md`. Tests are ordered pairs `(term holds)`, with
`t` for true and `nil` for false.

`instances` is an insertion-ordered alist of `(pairs . tests)`, where
`pairs` is a list of two-element lists `(variable actual)`. First
occurrences of substitution lists retain their tests. The empty dictionary
and an incompatible application both give `nil`.

`openings` is an ordered list of definition symbols or an insertion-ordered
alist of `(symbol . count)` entries for explicit unfolding counts.
`selector-openings` and `preserve` are lists of definition symbols and
protected terms, respectively. Pass `nil` for either omitted list.
`assume-premise` is `:none` to infer the option, or `t` or `nil` to
choose it explicitly.

| Call | Result | Failure |
|---|---|---|
| `(h1-recursion-recursive-instances proof application)` | The recursive instances of the definition applied in `application`. Variables retain the order of the original actual arguments. | A failure from looking up the definition, reading a term or substituting. |
| `(h1-recursion-selector-path term variable)` | The list of `(selector argument)` pairs from the root variable outward, or `nil` if the term has no such path. | A failure from indexing a malformed selector call. |
| `(h1-recursion-selector-equation proof variable actual selector-openings)` | The simplified selector equality under the cons assumption, or `nil`. | A proof failure. |
| `(h1-recursion-selector-bound proof selector variable)` | The built-in decrease Step for the selector symbol and root term. | A proof failure. |
| `(h1-recursion-structural-descent proof variable actual tests selector-openings)` | `(cons step-or-nil proof)` with the structural decrease Step if applicable and the resulting Prover. | A failure from inspecting the path or proving the decrease. |
| `(h1-recursion-descent-for proof variable actual tests selector-openings)` | `(cons step-or-nil proof)` with the additive or structural decrease Step if applicable and the resulting Prover. | A proof failure. |
| `(h1-recursion-prove-with-projections proof formula variable instances openings selector-openings preserve)` | Step proving `formula` by strengthened induction, or `nil` when there are no suitable projections. | A proof failure, including `unproved`. |
| `(h1-recursion-prove-from-calls proof formula openings selector-openings assume-premise preserve)` | `(cons step proof)` with the proof of `formula` and the resulting Prover. | A proof failure, including the last `unproved` if the induction attempts fail. |
| `(h1-recursion-prove-automatically proof formula)` | `(cons step proof)` with the proof by simplification or induction and the resulting Prover. | A proof failure, including `unproved`. |

In calls returning a pair, a failure occupies the value position so that
callers can retain any supporting entries added to the Prover. The constant
`*h1-recursion-atom*` is the prover symbol for Common Lisp `ATOM`.

`(h1-recursion-build proof)` prepares the derived Library and returns
the resulting Prover or a failure. The build adds its facts and entries in
the order of the Library recipes.

`recursive-instances` processes each recursive call when the walk reaches
it. An incompatible call ends the walk immediately.
