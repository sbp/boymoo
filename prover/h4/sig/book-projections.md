# List-spine projections

`p` is the Library used for the book tactics. Terms and Steps follow
`prover/sig/proof.md`. Evidence and rewrite rules are lists of Steps in
the order supplied. `provide` is a normalizer provider in the form
specified by `prover/h4/sig/tactics.md`. Pass `nil` for an absent provider
or an empty rewrite list.

`*h4-book-projections-keys*`, `*h4-book-projections-values*` and
`*h4-book-projections-rev*` are the symbols `ALIST-KEYS`, `ALIST-VALS`
and `REV`. `*h4-book-projections-projections*` lists the key projection
before the value projection.

| ACL2 call | Result |
|---|---|
| `(h4-book-projections-open-selected p call evidence provide rewrites)` | Equality Step obtained by unfolding `call` and normalizing its body. |
| `(h4-book-projections-list-equiv-shape formula)` | `(left right index)` for a matching implication, or `nil`. `index` counts from the compound term's head at index zero. |
| `(h4-book-projections-agrees-with-list-fix p call index)` | Step equating `call` with the version that applies `TRUE-LIST-FIX` to its argument at `index`, with the fixed call on the left. |
| `(h4-book-projections-list-equiv-proof p formula match)` | Step proving `formula`. `match` is a `(left right index)` list. |
| `(h4-book-projections-projection-revappend p projection first tail)` | Step proving that `projection` distributes over `REVAPPEND` of `first` and `tail`. |
| `(h4-book-projections-revappend-logical-view p)` | Two-element list of the equality Step for `REVAPPEND` in terms of `BINARY-APPEND` and `REV`, followed by the append associativity Step. |
| `(h4-book-projections-reverse-as-revappend p)` | Step equating `REVAPPEND` with a quoted NIL accumulator to `REV`. |
| `(h4-book-projections-projection-reverse p projection source)` | Step proving that `projection` commutes with `REV` on `source`. |
| `(h4-book-projections-projection-proof p formula)` | A Step for a recognized list equivalence or projection formula, or `nil`. |

Proof operations can propagate a failure. A malformed term can produce
a failure in the shape matcher. The dispatcher tries the projection
shapes when the list equivalence attempt yields one of the fallback
kinds in `prover/h4/notes/failures.md`.

With an on-demand provider, `open-selected` returns a normalizer request
when a reply is needed. Supply the reply and repeat the call as specified
in `prover/h4/sig/tactics.md`.
