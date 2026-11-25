# Single-statement proofs

`(t4-api-prove statement earlier library aids)` takes one statement string and
three lists of strings. Each string represents one input line and may end with
a newline. It returns `nil` if proof generation fails or the statement has no
proof obligation. A successful result is `(lemmas entry)`. `lemmas` is a list
of auxiliary entry strings in dependency order, and `entry` is the proof entry
string for the statement. The strings include their final newlines. Auxiliary
names have the prefix `PROVER-T4-`. Internal failures become `nil` at this interface.

`*t4-api-prefix*` is the string `"T4"`. Parsed symbols and terms, a `Proof`,
and a `BookLogic` use the forms in their owning books' signatures. `kind` is
the string at the head of an input line, and `data` is the list of its parsed
fields. Dictionaries retain insertion order. The ground name sets and the set of
normalized lines from `t4-api-given` are ordered by S-expression text.

| Call | Result | Failure |
|---|---|---|
| `(t4-api-ground)` | `(proof recursive packages)`, the ground Proof, the set of its recursive function names and the set of its package names. | None. |
| `(t4-api-line value)` | Line string `value` with its final newline appended if needed. | None for ASCII strings. |
| `(t4-api-read raw)` | `(kind data)` parsed from line `raw` after removing its last byte. | A reader failure. |
| `(t4-api-obligation kind data)` | The name of the proof obligation in the parsed statement, or `nil` if it has none. | A failure from inspecting the fields or detecting recursion. |
| `(t4-api-recursive kind data)` | Recursive function names of a `define` statement in definition order, or the empty list. | A failure from inspecting the fields or detecting recursion. |
| `(t4-api-statement raw)` | `(kind data recursive)` for line `raw`, where `recursive` is the list of recursive function names. | A reader or recursion detection failure. |
| `(t4-api-register tactic kind data recursive)` | The `BookLogic` with recursive functions, packages, mutually recursive groups, and evaluator facts registered as applicable. | A failure from inspecting or registering the statement. |
| `(t4-api-admit tactic choices raw)` | `(tactic choices)` with line `raw` admitted, registered, and indexed. `choices` is the list of choice rules in input order. | A failure from parsing, admission, registration, or indexing. |
| `(t4-api-given lines)` | `(tactic seen choices)` for the given library lines. `seen` is the set of distinct normalized lines, and `choices` is the list of choice rules in first-occurrence order. | A failure from parsing, admission, or building the tactic. |
| `(t4-api-clone base)` | The value of the `BookLogic` `base`, which can be used independently of `base`. | None on a `BookLogic`. |
| `(t4-api-enabled-functions hints)` | The function names from `ENABLE` forms within parsed `hints`, in traversal order with repeats. | None on parsed hints. |
| `(t4-api-aids lines)` | `(stored hints)`, a pair of alists keyed by function or theorem name. `stored` maps to `(measure relation)` and `hints` maps to the ordered list of enabled functions. | A failure from parsing or reading the fields. |
| `(t4-api-sections source)` | Consecutive proof sections of string `source`, each returned as a list of line strings with the line endings retained. | A failure when a line has no word after its first byte. |
| `(t4-api-rename source names)` | String `source` with complete tokens replaced by the alist `names`, keyed by written symbol tokens. | None on strings and a string-valued alist. |
| `(t4-api-entries source occupied)` | `(lemmas entry)` from proof text `source`, with auxiliary names derived by SipHash-2-4. `occupied` is the alist of facts in the statement context. | A failure when parsing or writing fails, or when auxiliary declarations conflict or collide with `occupied`. |
| `(t4-api-init-proof instance)` | The Proof `instance` with ground facts, definitions, and primitives. Pass `nil` to initialize a base Proof. | None. |
| `(t4-api-admitted-facts proof kind data choices)` | `(proof choices)` with the parsed statement's facts and any available choice recorded. Pass `:none` to skip choice discovery. | A failure from reading the statement or discovering a choice. |

The auxiliary-entry traversal and token scanner can also return `fuel`
when their recursion budget is exhausted.

## Session preparation

| Call | Result | Failure |
|---|---|---|
| `(t4-api-line-sequence value)` | The input list, with an empty string treated as the empty list. | A failure for any other value. |
| `(t4-api-prepared-given lines)` | `(tactic seen choices)` for the given library lines. The distinct normalized lines in `seen` and the choice rules in `choices` follow first occurrence. | A failure from parsing, admission, or building the tactic. |
| `(t4-api-recursive-names definitions)` | Names in definition order from the list of definition triples. | A failure from inspecting a definition. |
| `(t4-api-admit-statement tactic choices parsed)` | `(tactic choices)` with the `(kind data recursive)` statement admitted, registered, and indexed. | A failure from admission, registration, or indexing. |
| `(t4-api-proof-answer prefix tactic choices raw parsed name supplied)` | The answer from the prefix Proof, BookLogic, selector choices, normalized statement line, its `(kind data)`, obligation name, and `(stored hints)` aid dictionaries. | A failure from generation or serialization. |
