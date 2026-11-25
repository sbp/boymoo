# H4 proof interface

`(h4-api-prove statement earlier library aids)` takes a statement string and three groups of input lines. Each group may be a list of strings or a single string with line breaks. It returns `(lemmas entry)` on success. `lemmas` is the ordered list of auxiliary entry strings and `entry` is the statement's proof entry string. The final newlines are part of the result. Auxiliary names use the prefix `H4`. An input or proof failure gives `nil`.

A library context is `(:h4-api-library-context source world)`. `source` is the list of distinct library lines in first-occurrence order, and `world` is the initialized, admitted Tactics world. Parsed statements, Tactics worlds, Steps, and entries use the forms in the signatures of their owning books. Dictionaries are association lists in insertion order. A shared prelude is `(entries aliases)`, where `entries` is the list of renamed entry strings and `aliases` is the association list from original written names to renamed written names. Pass `(list nil nil)` for an empty shared prelude.

| Function | Arguments and result | Failure |
|---|---|---|
| `(h4-api-lines source)` | Sequence of lines, or a string containing lines. Returns the list of lines, preserving their terminators. | None on these forms. |
| `(h4-api-as-bytes line)` | Source line string. Returns the line with a final line feed, adding it if necessary. | None for source in the input alphabet. |
| `(h4-api-parsed line)` | Source line string. Returns the parsed Statement. | A failure from parsing. |
| `(h4-api-aid-info source)` | List of aid lines. Returns `(measures hints)`, with the alists keyed by function name and statement name, respectively, and each distinct measure-relation pair or hint in first-occurrence order. | A failure from parsing an aid. |
| `(h4-api-admit world statement)` | Tactics world and parsed Statement. Returns the resulting world with the statement admitted. | A failure from admission. |
| `(h4-api-copy-world world)` | Tactics world. Returns its working copy. | None on a world. |
| `(h4-api-ground-world)` | The initial Tactics world with empty book function, choice, and template collections. | A failure from initialization. |
| `(h4-api-library-context-init source)` | List of library lines. Returns the context after admitting each distinct line in order. | A failure from initialization, parsing, or admission. |
| `(h4-api-library-context-prefix context earlier)` | Library context and list of earlier lines. Returns a working world with the new earlier lines admitted, each distinct line once. | A failure from parsing or admission. |
| `(h4-api-library-context source)` | List of library lines. Returns the initialized library context. | A failure from initialization, parsing, or admission. |
| `(h4-api-core-support)` | Returns `(entries facts definitions)` for the core support. Entries follow declaration order, facts follow the corresponding entry names, and definitions follow definition order. | A failure from building support. |
| `(h4-api-support-selection world proofs source)` | Tactics world, conclusion Steps, and final entry source. Returns the relevant auxiliary entries in the world's entry order. | A failure from writing an entry name. |
| `(h4-api-install-core-support world)` | Tactics world. Returns the world extended with core support. | A failure from core support or a failed assertion. |
| `(h4-api-use-core-support world)` | Tactics world. Returns the world with core support, and the pointwise lemma when available. | A failure from core support or a failed assertion. |
| `(h4-api-warrant-support definitions)` | A list of `(name formals body)` definitions. Returns `(facts definitions filters shared)` for the warrant prelude. | A failure from building or writing support. |
| `(h4-api-prepare-warrant world formula)` | Tactics world and warrant theorem formula. Returns `(cons shared world)` with the extended world. | A failure from building support or a failed assertion. |
| `(h4-api-optional result)` | Returns the attempted value when successful or `nil` for a failure. | None. |
| `(h4-api-special world statement)` | Tactics world and parsed Statement. Returns `(lemmas entry)` if a specialized recipe applies, otherwise `nil`. | A failure from preparing, proving, or writing the entry. |
| `(h4-api-extra-theorem world statement)` | Tactics world and parsed Statement. Returns `(cons (kind arguments proofs) world)` for the first successful additional theorem recipe, or `(cons nil world)` if none succeeds, with the resulting world in each case. | A failure from reading the theorem formula. |
| `(h4-api-solve context earlier statement measures hints)` | Library context, earlier line list, statement string, and relevant measure and hint alists. Returns `(lemmas entry)` on success or `nil` on failure. | None. |
| `(h4-api-build-proof context earlier statement measures hints)` | As for `h4-api-solve`, with a parsed Statement. Returns `(lemmas entry)` on success or `nil` for a statement already in the world. | A failure from building or writing the proof. |
| `(h4-run-proof-dependencies step)` | Conclusion Step. Returns the set of named facts reached in the proof, listed in first-visit order as the stack is popped. | None on a Step. |
| `(h4-run-entry-sources world last final-source)` | Tactics world, conclusion Step, and final entry source string. Returns `(step-count source)` pairs for required entries in declaration order. | A failure from writing an entry name. |

`*h4-api-warrant-definitions*` is the ordered list of symbols whose definitions can be used in warrant support.

The interface's Tactics world is `(:h4-api-world library functions choices filters)`. `library` is the underlying H4 Tactics Library. `functions` lists constrained and chosen function names in first-occurrence order. `choices` is an alist of `(name . fields)` entries in declaration order. `filters` is the list of filter names for a prepared warrant. `h4-api-make-world` takes the four fields in order. The functions `h4-api-world-library`, `h4-api-world-functions`, `h4-api-world-choices`, and `h4-api-world-filters` take a world and return their named field. `h4-run-entry-sources` receives the underlying Library.

`*h4-api-prefix*` is the exported name prefix, `"H4"`. The warrant certificate's emitter is the operation in `badge-table.md` that appends a lemma entry and adds its fact in emission order.

The dependency traversal may return `fuel` on exhaustion or propagate a failure for a malformed Step.
