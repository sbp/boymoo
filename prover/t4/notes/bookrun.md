# Book proof entries

A proof Entry carries the obligation name, proof text, proof step count
and skip reason. The section splitter recognizes LF, CRLF and CR
boundaries. Assembly visits sections in source order and shares
identical declarations among entries.

A constraint may have a witness from the primary proof, evaluator
witness search or simple witness search. `t4-bookrun-book-entry`
takes those results and constructs the Entry. Its signature is in
`prover/t4/sig/bookrun.md`.
