# Single-statement proof interface

`(h1-api-prove statement earlier library aids)` takes one statement line
and three groups of input lines. Each group can be a list of line strings,
a string containing line breaks, or `nil` for an empty group. `earlier`
provides the statement prefix, `library` supplies the library declarations,
and `aids` supplies measure hints.

The proof result is `(lemmas entry)`. `lemmas` lists auxiliary entry
texts in dependency order. `entry` is the text of the statement's proof
entry. Each text includes its trailing newline. An unsuccessful attempt
returns `nil`.

`*h1-api-prefix*` is the string `"H1"`.
