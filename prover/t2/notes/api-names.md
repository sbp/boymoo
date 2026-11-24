# Private helper names

The token scanner recognizes qualified symbols from their `::` separator.
It uses spaces, parentheses, and line terminators as delimiters and
preserves first-occurrence order. The proof names already assigned in an
attempt determine which references the next helper must rewrite.

For the digest, `t2-api-names-private-entry` normalizes the helper's own
declared names to placeholders and resolves its earlier bindings.
`t2-api-names-digest` writes the SipHash-2-4 digest as sixteen uppercase
hexadecimal digits. Private labels combine a prefix, this digest, and
a stem from the declared name. The occupied names are checked before the
bindings are installed.
