# Statement admission and proof output

`library` is a Library as specified in `prover/sig/library.md`. Names, terms and Steps have the forms in `prover/sig/proof.md`. `kind` is the statement word as a string. `fields` is its list of parsed fields. Byte strings are ACL2 strings.

| Call | Result | Failure |
|---|---|---|
| `(h3-generate-admit library kind fields)` | Library with the definitions or facts of the statement. Replaced declarations retain their insertion positions. | A failure for malformed fields. |
| `(h3-generate-serialize-theorem library name result)` | Two-element list of the total step count and the proof text. The dependencies are printed in Library entry order, followed by the theorem. | A failure from building or writing the proof, or `Fuel`. |
| `(h3-generate-reason name)` | Reason string for the unqualified name string. | None for a string. |
| `(h3-generate-quote-input contents)` | Byte string containing the quoted checker input for the given byte string. | None for a byte string. |

`*h3-generate-default-reasons*` is the ordered association list of name strings to reason strings.

`(h3-generate-serialize-theorem-visit n entry entries fact-lines needed)` adds the entries reachable from `entry` to `needed`, retaining names in order of first discovery. `entries` maps names to entry records and `fact-lines` maps complete citation lines to names, both in insertion order. The initial fuel `n` is `1000000`. The visitor can return a failure for an absent cited entry or exhausted fuel.
