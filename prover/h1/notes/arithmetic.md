# Arithmetic requests

`h1-arithmetic-query` evaluates a recipe using a table of replies to
requests for proof steps, helper entries, and rule updates. The
dispatcher carries the resulting prover to the next request. A helper
reply pairs the new fact with the resulting library. A rule update
returns `nil` after installing the updated rules.

The signed countdown and exponentiation recipes request their steps in
proof order. An omitted induction limit is represented by `:none`,
which lets the book prover apply its case limit.
