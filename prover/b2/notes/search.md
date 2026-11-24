# Search state

The Search record carries the fact buckets, equality index, active
goals, and remaining inference budget. Replacing its Library lets it
use current clauses for indexed facts. Inference branches use the
failure kinds in `prover/b2/notes/failures.md` to select alternatives.

`grep -nE 'b2-search-search-(with-lib|init|prove)|b2-search-rejected-step-p' prover/b2/search.lisp` shows the proof operations. The command was run on 2026-11-23.
