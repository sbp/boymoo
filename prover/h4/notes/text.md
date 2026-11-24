# Proof text and line handling

`h4-api-lines` accepts source lines or splits a source string at line
breaks while keeping line terminators. A carriage return followed by a
line feed is a single break.

`h4-book-run-lines` has three modes. `:bytes` preserves carriage return
and line feed breaks, including their paired form. `:file` splits on line
feeds. `:text` combines paired line breaks, normalizes carriage returns
to line feeds and also recognizes the ASCII vertical separators. The
result labels use `h4-book-run-decimal-chars` to check for decimal digits.

`h4-api-encoding-ascii-text` checks the character range of proof text.
`h4-api-encoding-rename` scans the source for substitutable written names.
The encoding book uses proof steps and their dependencies to write a
canonical entry.
