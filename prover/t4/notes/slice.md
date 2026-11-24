# Proof generation

The slice enumerates measure candidates in proof search order and
selects the first successful measure. For a constraint, an unsuccessful
primary witness attempt can invoke the evaluator and simple witness
tactics.

A definition-generation request receives the generated value or its
failure. A used-prelude request receives the result of
`t4-slice-used-prelude`. `t4-slice-book-entry-with-tactic` returns the
Entry, Proof and BookLogic for further obligations.
