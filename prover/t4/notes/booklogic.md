# The tactic context

A BookLogic contains the Library and the indexes and budgets used by
theorem search. Rule lookup uses the leading function of a term and,
where available, the leading function of its first argument. The
context also holds evaluator equations, recursive names, and mutual
recursion groups.

`t4-booklogic-booklogic-init-with-proof` indexes an admitted Proof.
A session can retain definition sizes keyed by name and definition
body. The body check allows a tactic to introduce a new definition
or replace a definition during an attempt.

Some tactics ask for proof operations by returning a request.
`t4-booklogic-tactic-reply` answers with the resulting context and any
Evidence. A constant computation can change the full BookLogic, and the
reply's Library is obtained from that context. A reply that retains
the Library on failure lets the next tactic use the auxiliary entries
already produced.

The tactic entry points and their request and reply forms are in
`prover/t4/sig/booklogic.md`. Search failure kinds are documented in
`prover/t4/notes/failures.md`.
