# Floor split

The `lib` argument is a Library as specified in `prover/sig/library.md`. Terms, Steps and RulerFacts have the forms in `prover/sig/proof.md` and `prover/t2/sig/tactics.md`. Definitions, Calls and measures have the forms in `prover/sig/termination.md`.

| ACL2 call | Arguments and result | Failure |
|---|---|---|
| `(t2-floor-split-quotient-bracket lib)` | Returns the Library with `FLOOR-SPLIT-BOUNDS` available. Returns the input Library when the fact is present. | A failure from proof construction. |
| `(t2-floor-split-scheme term parent)` | Terms `term` and `parent`. Returns `(floor complement-p)` for a recognized split. The second field is `t` for the complementary part and `nil` for the quotient. Returns `nil` for an unrecognized split. | A failure from reading a malformed application. |
| `(t2-floor-split-decrease lib split hypotheses)` | Split as returned by `scheme`, and RulerFacts. Returns `(step library hypotheses)` with the decrease Step and the resulting Library and RulerFacts. | A failure from looking up hypotheses or constructing a proof. |
| `(t2-floor-split-definition lib definitions calls measures)` | List of definitions, list of Calls in source order, and insertion-ordered measure alist. Returns `(cons entry library)`, with `nil` for the entry when the tactic does not apply. | A failure from looking up a measure, reading a term or constructing a proof. |

`definition` emits proofs in the order of each obligation clause's first occurrence.
