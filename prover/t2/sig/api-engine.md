# Proof context and generation

Events and Obligations have the forms in `prover/t2/sig/books.md`.
Generators have the form in `prover/t2/sig/tactics.md`. Strings carry the text
of proof input and output, including line terminators. Dictionaries use
association lists in first-insertion order.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t2-api-engine-lines source)` | The lines of a string with their terminators retained, or the list supplied as `source`. A source of `nil` has no lines. | None for these inputs. |
| `(t2-api-engine-event source)` | Event parsed from the supplied source line. | A failure from parsing the line. |
| `(t2-api-engine-core)` | Generator built with an empty stored measure dictionary. | A failure from building the Library. |
| `(t2-api-engine-library-measures)` | Default dictionary from function names to lists `(measure relation)`, in measure source order. | None. |
| `(t2-api-engine-aids-for aids)` | List `(measures hints)` from the source line list `aids`. | A failure from parsing a line or its fields. |
| `(t2-api-engine-enrich generator)` | `(cons complete generator)` where each successful lemma family extends the Generator's Library and `complete` is true if every family succeeded. | None for a Generator. |
| `(t2-api-engine-base library book)` | List `(generator complete)` for the given library source lines, with enrichment attempted if `book` is true. | A failure from loading the given events or building the base Library. |
| `(t2-api-engine-context library earlier book)` | List `(generator complete)` as in `base`, with the source lines `earlier` then admitted. | A failure from `base` or from admitting the preceding events. |
| `(t2-api-engine-guessed-termination generator data)` | List `(lib entry)` for the first successful count or length measure on corresponding arguments. `data` is the definition event's field list. | `Unproved` when no trial succeeds, or a failure from reading the definitions or constructing the proof. |
| `(t2-api-engine-generate generator target hints stored)` | List `(lib entry)` for the proof of Obligation `target`. `hints` maps names to hints and `stored` maps function names to `(measure relation)` pairs. | A failure from reading or proving the obligation. |
| `(t2-api-engine-prove statement earlier library aids prefix)` | The two-element list `(helpers entry)` of proof text, with private proof names assigned for string `prefix`, or `nil` when no proof is returned. `statement` is one source line and the three line groups are strings, lists of strings, or `nil`. | A failure from input preparation or proof output, or a proof failure that is outside the recipe's recovery cases. |

`*t2-api-engine-failures*` lists the failure kinds handled by
the recovery paths in generation and proof search.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t2-api-engine-obligation statement event)` | The Obligation for a source line and its parsed event, or `nil` if no tactic applies. | A failure from the event or from reading its fields. |
| `(t2-api-engine-proof-text-parts result)` | The list `(helpers entry used)` with the ordered helper entries, the main entry's source text and the Library's fact dictionary. `result` is `(lib entry)` from `generate`, or a failure. | A failure from `result` or from selecting the proof entries. |
