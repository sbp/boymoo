# Strict lexicographic order

`library` is the B2 Library. Terms, names and Steps have the forms in
`prover/sig/proof.md`. These functions can return a failure from proof
construction.

| Call | Result |
|---|---|
| `(b2-strict-order-pieces library evidence)` | The two conjunct Steps obtained by opening the strict comparison proved by Step `evidence`. |
| `(b2-strict-order-flipped-distinct library a b evidence)` | The Step proving `b` distinct from `a`, given terms `a` and `b` and a Step proving `a` distinct from `b`. |
| `(b2-strict-order-strict-order library name formula)` | The Step proving theorem term `formula` for the given theorem symbol `name`. |

The symbol constants are `*b2-strict-order-strict*` (`<<`),
`*b2-strict-order-lex*` (`LEXORDER`), `*b2-strict-order-total*`
(`LEXORDER-TOTAL`), `*b2-strict-order-anti*` (`LEXORDER-ANTI-SYMMETRIC`),
and `*b2-strict-order-trans*` (`LEXORDER-TRANSITIVE`).

`*b2-strict-order-order-theorems*` is the set of theorem symbols, listed
in ascending order of their serialized forms. It comprises
`<<-IRREFLEXIVE`, `<<-IMPLIES-LEXORDER`, `<<-ASYMMETRIC`, `<<-TRANSITIVE`,
and `<<-TRICHOTOMY`.
