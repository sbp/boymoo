# Bounds on scan indices

Terms, Steps and Libraries have the forms in `prover/sig/proof.md` and
`prover/sig/library.md`. Evidence and its queries have the forms in
`prover/t3/sig/logic.md`. Each substitution is a list of `(formal actual)`
pairs in formal parameter order. Substitutions are kept in order of first
occurrence as the leaves are visited. Established evidence facts retain
their insertion order when updated.

The symbol constants are `*t3-scan-skip-alternative*`,
`*t3-scan-skip-bound*`, `*t3-scan-whitespace*`,
`*t3-scan-whitespace-bound*`, `*t3-scan-search*`, `*t3-scan-search-start*`,
and `*t3-scan-search-bound*`.

Each proof operation below can return a failure in place of its entire result.
In the inference calls, the result pairs the resulting Library with the
resulting Evidence, with the Library in the Evidence updated as well when
both arguments hold the same Library.

| Call | Result |
|---|---|
| `(t3-scan-index-claim index result)` | The proposition that a nonzero `result` is an integer greater than `index`. |
| `(t3-scan-scan-index-bound lib)` | The Library extended by the alternative-skip index lemma. |
| `(t3-scan-infer-skip-result lib term evidence)` | `(cons lib evidence)` after deriving the type and strict lower bound of a nonzero alternative-skip result, if applicable. |
| `(t3-scan-conclusion lib conditional proof)` | A Step establishing `conditional` with `proof` for its true branch and quoted `T` for its false branch. |
| `(t3-scan-typed-pair lib first second)` | A Step proving the conjunction of the first literals of the two Steps, in input order. |
| `(t3-scan-weak-after-advance lib old new result evidence advance result-type weak)` | `(cons step evidence)` for `old <= result`, from a strict advance and a weak bound at `new`. `result-type` is a Step for integrality of `result`. |
| `(t3-scan-induction-result lib target formals formula measure substitutions evidence)` | `(list step substitutions evidence)` with the instantiated induction hypothesis for recursive call `target` and the resulting substitutions and Evidence. |
| `(t3-scan-search-claim index bound target)` | The proposition that a true `target` is an integer at least `index` and that both endpoints are integers. |
| `(t3-scan-search-index-bound lib)` | The Library extended by the forward-search index lemma. |
| `(t3-scan-whitespace-claim index bound value)` | The proposition that `value` is an integer at least `index`, under the integer endpoint and order assumptions. |
| `(t3-scan-whitespace-index-bound lib)` | The Library extended by the whitespace-scan index lemma. |
| `(t3-scan-infer-whitespace-result lib term evidence)` | `(cons lib evidence)` after deriving the type and weak lower bound of a whitespace-scan result. |
| `(t3-scan-search-application lib term nonnil)` | A Step equating `term` to its forward-search call, given the Step `nonnil` proving `term` true. |
| `(t3-scan-infer-search-result lib term evidence)` | `(cons lib evidence)` after deriving the type and bounds of a non-NIL search result, if applicable. |
| `(t3-scan-infer-scan-result lib term evidence)` | `(cons lib evidence)` after inferring types and bounds for the recognized scan results in `term`, visiting the operands of sums in order. |

The leaf functions return `(cons step substitutions)` with the
proof for one result path and the substitutions after visiting it.
`tests` is the signed test list for that path. A failure is the entire result.

| Call | Result |
|---|---|
| `(t3-scan-scan-index-bound-leaf value tests lib index formals formula measure template substitutions)` | Alternative-skip leaf proof. |
| `(t3-scan-search-index-bound-leaf result tests lib index bound formals formula measure substitutions)` | Forward-search leaf proof. |
| `(t3-scan-whitespace-index-bound-leaf value tests lib index bound formals formula measure template substitutions)` | Whitespace-scan leaf proof. |
