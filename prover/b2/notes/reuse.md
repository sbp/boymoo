# Proof replay

A retained proof records the names and clauses of the required facts in
order of first mention in the proof text. Replay checks them against the
available clauses and installs missing support in declaration order.
A conflicting support declaration prevents replay.

`grep -nE 'b2-reuse-(required-facts|compiled-replay|replay-missing)' prover/b2/reuse.lisp` shows the proof operations. The command was run on 2026-11-23.
