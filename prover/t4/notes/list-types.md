# List result types

The list type tactics request arithmetic setup, fact and equation
search, and proofs using specified definitions. A constructor typing
call carries the Library and Evidence in the reply. A selector
proof can use the Library returned with a failed attempt to prove
the goal by contradiction.

`t4-list-types-count-item` counts occurrences of an equal term in an
ordered list. Request forms are in `prover/t4/sig/list-types.md`.
