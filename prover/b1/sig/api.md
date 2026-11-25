# B1 certificate interface

`(b1-api-prove statement earlier library aids)` takes one statement string and three ordered lists of line strings. Each input line may end with a newline. A result of `(lemmas entry)` contains auxiliary entry strings in dependency order and the obligation entry string. The strings include their final newlines. Auxiliary names begin with `PROVER-B1-`. An unsuccessful call returns `nil`. The package is `BOYMOO-PROVER`.

`*b1-api-prefix*` is the string `"B1"`.

A Context has the form `(:b1-api-context world seen formulas facts names)`. `world` is a BookProof, `seen` is a list of distinct raw input lines, `formulas` is an insertion-ordered alist from terms to fact names, `facts` is a FactIndex, and `names` is a list of distinct occupied symbols. The two sets have no iteration order observable through the interface. `b1-api-context-world`, `b1-api-context-seen`, `b1-api-context-formulas`, `b1-api-context-facts` and `b1-api-context-names` each take a Context and return its named field directly.

The API reader uses the shared Reader representation. The proof world for an individual call is a BookProof. An individual call starts with the prepared world, and subsequent updates produce a separate value.

| ACL2 call | Arguments and result | Failure |
|---|---|---|
| `(b1-api-raw value)` | Remove a single trailing line feed from the string `value`. | A failure for a nonstring value. |
| `(b1-api-parse raw)` | Parse a line string `raw` without its final newline. Return `(word data)`, where `word` is a string and `data` is the list of parsed fields. | A failure from reading the line. |
| `(b1-api-acl2-imports)` | Return the ground ACL2 import map, keyed by symbol label. | None for the ground theory. |
| `(b1-api-package-fact data)` | Return `(name term)` for the parsed package fields `data`. | Failure on malformed fields. |
| `(b1-api-choice-fact-choose arguments bound)` | Return the substitution alist for the choice call `arguments` and the list `bound` of choice variables. | None on parsed fields. |
| `(b1-api-choice-fact data)` | Return `(name term)` for the parsed choice fields `data`. | Failure from fields or term construction. |
| `(b1-api-context-init world seen formulas facts names)` | Construct a Context from its fields, constructing a FactIndex from `world` when `facts` is `:none`. | Failure from indexing. |
| `(b1-api-context-extend context lines)` | Extend `context` with the list of line strings `lines`, indexing facts in input order after existing rules. Duplicate raw lines are ignored. | Failure from parsing, admission, or indexing. |
| `(b1-api-ground)` | Construct the Context for the ground theory with the library recipes built. | Failure from construction or indexing. |
| `(b1-api-given lines)` | Extend the ground Context with the list of line strings `lines`. | Failure from construction or extension. |
| `(b1-api-prefix given lines)` | Extend the Context `given` with a list of earlier line strings. | Failure from extension. |
| `(b1-api-measures aids)` | Read measure records from the list of line strings `aids`. Return the insertion-ordered alist from function symbols to measures, keeping the last eligible record for each symbol. | Failure from reading a measure line. |
| `(b1-api-names-in source)` | Return matches for unquoted local names in proof text `source`, in source order. A match is `(spelling start end)`, with zero-based offsets and an exclusive `end`. | A failure for an unclosed quote. |
| `(b1-api-references source names)` | Return the distinct spellings in `source` that occur in the list `names`, in first-occurrence order. | Failure from scanning the text. |
| `(b1-api-rename source names)` | Rename unquoted local names in text `source` with the alist `names` from original spellings to replacement spellings. | Failure from scanning the text. |
| `(b1-api-certificate entries source occupied)` | Select auxiliary dependencies from ordered library `entries` for obligation text `source`, with occupied symbols `occupied`. Return `(lemmas entry)` with private names. | A failure for a collision or missing dependency, or from reading or writing a name. |
| `(b1-api-theorem-entry world name formula proof)` | Write the theorem `name` for `formula` from the Step `proof` in `world`. Pass `nil` for a missing Step. | A failure if the theorem cannot be discharged or written. |
| `(b1-api-witness-entry world name data recipe index)` | Write the witness entry for constraint `name` with parsed fields `data`, witness recipe identifier `recipe`, and FactIndex `index`. A `nil` recipe selects the small-witness search. Return `(cons text world)` with the updated world. | Failure from the recipe, proof validation, or writing. |
| `(b1-api-solve world context word data name calls measures)` | Try the recipes in order for statement `word` with fields `data`, name `name`, recursive `calls` and stored `measures`, using `world` and the prefix `context`. Return `(world entry)` with the successful world and entry text. | A failure if every recipe fails or a direct proof operation fails. |

## Reader, proof, and context operations

| ACL2 call | Arguments and result | Failure |
|---|---|---|
| `(b1-api-callproof-fork world)` | Return the supplied `world`, whose facts, definitions, and auxiliary entries the call can use as its starting point. | — |
| `(b1-api-ground-world)` | Return the built BookProof with the ground package facts installed. | A failure from construction. |
| `(b1-api-context-for library earlier)` | Return the context for the library and earlier line lists. The earlier lines are extended in two groups at the last multiple of 64. | A failure from construction or extension. |
| `(b1-api-prove-in-context statement earlier library aids)` | Take the same arguments and return the same successful results as `b1-api-prove`. Propagate failures to the caller. | A failure from reading, constructing the context, proving, or exporting. |
| `(b1-api-ascii-text text)` | Return the input string when its characters are ASCII. | A failure for a character outside ASCII. |

The reader and auxiliary text scanner return `fuel` if a scan exhausts its recursion counter.

## Prepared contexts

The constant `*b1-api-acl2-imports*` is the ground import map
returned by `b1-api-acl2-imports`.

| ACL2 call | Arguments and result | Failure |
|---|---|---|
| `(b1-api-make-context world seen formulas facts names)` | Construct a Context using the given fields, including an already built FactIndex. | None. |
| `(b1-api-context-add-statement word data world formulas names additions)` | Admit a parsed context line. Return `(world formulas names additions)` with the updated fields. The additions alist keeps the last clause at each name's first insertion position within the group. | Failure from admission or term construction. |
| `(b1-api-context-finish context updated)` | Finish one group of context lines. The argument `updated` is `(seen world formulas names additions)`. Return the resulting Context. | Failure from indexing. |
| `(b1-api-prove-prepared context word data name calls measures)` | Prove and export a new parsed obligation using the Context and measure alist. The caller checks that the raw line has not already been seen. | Failure from proving or exporting. |
