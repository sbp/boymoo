# T2 proof interface

`(t2-api-prove statement earlier library aids)` takes the text of one
statement and three groups of input lines. Each group can be `nil`, a list
of strings, or a string containing one or more lines. The groups preserve
their input order. `earlier` supplies preceding statements, `library`
supplies the given library statements, and `aids` supplies measures and
proof hints.

The result is `nil` when no proof is returned. Success is the two-element
list `(lemmas entry)`, where `lemmas` is the list of helper entry strings
in proof order and `entry` is the main proof entry string. Newlines in
the returned strings are part of the proof text. The interface also returns `nil` when an attempt fails.

`*t2-api-prefix*` is the string `"T2"` used to name the helper entries.
The package is `BOYMOO-PROVER`.
