# Private names in proof text

Source text, prefixes, and tokens are ACL2 strings. Symbol data and terms
have the forms in `prover/sig/proof.md`. A name map is an association list of
`(original . replacement)` entries in insertion order. A list of bindings
contains `(original replacement)` pairs in their supplied order. Forming a
name map from bindings retains the first position and last replacement for
each original.

| Function | Arguments and result |
|---|---|
| `(t2-api-names-parsed raw)` | Proof line string. Returns `(word fields)`, where the word is a string and fields are frozen reader data. |
| `(t2-api-names-fields value size)` | Returns the supplied list of `size` fields or the one-character strings of a string of length `size`. |
| `(t2-api-names-term-with-names term names)` | Term and name map. Returns the term with its call operators renamed. |
| `(t2-api-names-rewrite-line raw names private)` | Proof line, name map and Boolean. Returns the resulting line, retaining `raw` when the parsed fields are identical. |
| `(t2-api-names-rename source bindings private)` | Source string, list of bindings and Boolean. Returns the renamed source as a string. |
| `(t2-api-names-source-tokens source)` | Source string. Returns distinct tokens containing `::`, in first-occurrence order. |
| `(t2-api-names-dependencies source names)` | Source string and name map. Returns bindings for the names occurring as tokens, in name map order. |
| `(t2-api-names-private-entry source declared before prefix)` | Source string, list of declared names, earlier bindings and private prefix string. Returns `(own source)`, with the new bindings in declaration order and the rewritten text. |
| `(t2-api-names-namespace helpers entry prefix used)` | List of `(kind name counts source)` helper entries, main entry source string, prefix string and association list of occupied names. Returns `(helper-sources entry-source)`, retaining helper order. |

`t2-api-names-source-tokens` has no failure. The other functions can return a
failure from parsing, validating, or writing their arguments. Namespace also
returns a failure if a private name is already occupied. Its `used` map
has the same form as the facts of a Proof.

`*t2-api-names-token*` lists the scanner's delimiter characters. A token is a
maximal nonempty sequence of characters between delimiters.
