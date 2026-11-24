# Proof-owned names and entries

The prefix string is `*h4-api-encoding-prefix*`. The owner string is
`*h4-api-encoding-owned*`. Proof source and written names are byte strings
represented as ACL2 strings. Prover names and library entries use the forms
in `prover/sig/proof.md` and `prover/sig/library.md`.

| Call | Result and failures |
|---|---|
| `(h4-api-encoding-rename source aliases names-only)` | The source with aliases substituted. The aliases are an insertion-ordered alist of `(old . new)` written names. Pass `nil` for the usual token scan or `t` for the names-only scan. |
| `(h4-api-encoding-owned-entry kind name source dependencies names-only)` | A two-element list of the new written name and the revised source. The kind string is `"lemma"` or `"define"`. Dependencies are two-element lists `(old new)` in alias insertion order. The name includes the uppercase hexadecimal SipHash-2-4 digest of the source after dependency substitutions. Invalid names, kinds, declaration text or non-ASCII output can produce a failure. |
| `(h4-api-encoding-owned-entries entries inherited names-only)` | A two-element list of the revised source strings in entry order and the resulting alias pairs `(old new)` in insertion order. Inherited aliases are pairs in insertion order. Pass `nil` for an empty inherited list or the usual token scan. Entry conversion or name writing can produce a failure. |

Renaming requires aliases and a literal occurrence of `ACL2::H4-` or
`ACL2::SELF-` somewhere in the source. A name candidate has one of those
stems and a nonempty suffix ending before a space or right parenthesis.
A left parenthesis, a line feed or the end of the source before that
terminator makes the candidate fail.

In the usual scan, a name candidate begins after a space or left
parenthesis. A double-quoted string or bar-delimited span is a single
text token and can match an alias as a whole. Substitutions apply outside
`(COMMON-LISP::QUOTE ...)` forms. The names-only scan checks for the two
stems at any position, including within quoted data, strings and
bar-delimited spans.

`(h4-api-encoding-ascii-text source)` returns `source` when every
character code is below 128, or a generic failure otherwise.

`(h4-api-encoding-owned-entries-with-cache entries inherited names-only cache)`
returns `(cons result cache2)`, where `result` is the value of
`h4-api-encoding-owned-entries`, including a failure. The cache keeps at most
512 renamed entries keyed by kind, name, source, dependency aliases, and
`names-only`. Pass `nil` for an empty cache or `:uncached` to compute each entry.

`(h4-api-encoding-remember key value cache capacity)` returns an alist of
at most `capacity` entries with the given association first. The remaining
entries keep their relative order. The capacity is positive.
