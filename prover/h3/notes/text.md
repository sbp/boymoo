# Proof text

`h3-api-proof-lines`, `h3-books-source-lines`, and
`h3-generate-lines-with-endings` recognize LF, CR, and CRLF and
retain the complete terminator. The slice tactic dispatches on ASCII
theorem labels, checked by `h3-api-ascii-characters-p`.
