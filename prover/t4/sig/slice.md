# Slice proof generation

`prefix` and `proof` are Proof objects from `prover/sig/proof.md`. When a
containing library holds the Proof, its caller extracts and replaces the
Proof through that library's accessors. A choice list is in admission order.
`kind` is a statement word and `data` is its field list. `stored` is an
insertion-ordered dictionary of supplied measures with entries
`(function . (measure relation))`. A candidate has the form
`(measures mode)`, where `measures` is the dictionary of functions to terms
in definition order. Modes are strings, with `"application"` and
`"unification"` identifying the respective phase tactics.

| Call | Result | Failure |
|---|---|---|
| `(t4-slice-admitted-facts proof kind data choices)` | `(updated-proof updated-choices)`. Pass `:none` to omit choice discovery. A choice list, including `nil`, enables discovery and receives each new choice at the end. | A failure from inspecting the statement or discovering a choice. |
| `(t4-slice-used-prelude entries target)` | `(steps source)` for the transitive prelude and the target in source order. Each entry is the four-field result of `proof-proof-entry`. | A failure from writing an entry name or malformed entry data. |
| `(t4-slice-proof-library prefix library-type)` | A Library containing the prefix's facts and definitions, with the requested recipes built. Pass `:structural`, `:ordinals`, or `:lexicographic` to choose the proof recipes. | A failure from building the library. |
| `(t4-slice-selector-path term formal)` | Whether the term follows one or more CAR or CDR selectors from the given formal. | A failure on a malformed selector path. |
| `(t4-slice-inferred-measures definitions calls)` | Ordered inferred candidates from definitions and Calls in the shared termination representation. | A failure from inspecting terms or actual arguments. |
| `(t4-slice-measure-candidates definitions calls stored)` | Ordered candidate list. A measure attempt consumes these in order and stops at the first success. | A failure from selecting a candidate. |
| `(t4-slice-measure-entry prefix data stored)` | `(steps source)` from the first successful measure attempt. | `Unproved` after the candidates fail, or an unhandled failure. |
| `(t4-slice-measure-proofs prefix definitions calls measures mode)` | `(steps source)` for the measure entry with its used prelude. | `Unproved` for an unresolved comparison or a failure from constructing the proof. |
| `(t4-slice-generate prefix kind data stored choices)` | `(cons (list steps source) proof)` with the generated measure or witness and the resulting Proof. | `Unproved` when generation fails, or another failure from the proof routines. |
| `(t4-slice-book-entry proof tactic choices raw kind data name stored hints)` | `(cons entry proof)`, where `entry` is the Entry from `prover/t4/sig/bookrun.md` and `proof` is the resulting prefix Proof. `tactic` is BookLogic and `hints` is a dictionary from names to ordered lists of enabled functions. | A failure outside the proof failures handled by book entry generation. |
| `(t4-slice-quoted-bytes source)` | The serialized ACL2 Core quotation of the byte string. | None. |

Unsuccessful measure or witness generation can return
`(:failure "Unproved" "")`. The retry conditions are described in
`prover/t4/notes/failures.md`.

`(t4-slice-book-entry-with-tactic proof tactic choices raw kind data name stored hints)`
uses the same arguments and can return the same failures as `t4-slice-book-entry`.
Its successful result is `(entry proof tactic)`, including the BookLogic with
the changes made by theorem or simple witness search.
