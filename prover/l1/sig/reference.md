# Embedded checker input

Input and output text are ASCII strings.
The prover symbol constants are `*l1-reference-plan*`,
`*l1-reference-lines*`, `*l1-reference-previous*`,
`*l1-reference-current*`, `*l1-reference-n*`, `*l1-reference-tail*`,
`*l1-reference-ground*`, `*l1-reference-library*`,
`*l1-reference-statements*`, `*l1-reference-w*`,
`*l1-reference-drop*`, `*l1-reference-decode*`,
`*l1-reference-verdict*`, `*l1-reference-check*`,
`*l1-reference-lambda*`, `*l1-reference-coerce*` and
`*l1-reference-stringp*`. The constants `*l1-reference-list*` and
`*l1-reference-string-empty*` are the quoted list designator and quoted
empty string datum.

| Call | Arguments and result | Failure |
|---|---|---|
| `(l1-reference-boymoo name)` | Form a `BOYMOO` symbol from its name string. | None. |
| `(l1-reference-program)` | Return the four definition lines for the embedded checker, in definition order. | Writer failure. |
| `(l1-reference-suffix-length line-bytes previous)` | Length of the longest common suffix of the two strings. | None for byte strings. |
| `(l1-reference-encoded-lines source)` | Return the written quoted plan for the proof source string, visiting rows in reverse order and keeping the previous eligible constructor row as the suffix reference. | Writer failure. |
