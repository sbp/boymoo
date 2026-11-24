# Truncation intervals

Truncation bounds use signed cases for the dividend and divisor.
The proof compares the quotient with the appropriate pair of bounds
for each branch and combines the branch Steps.

`grep -nE b2-truncate-intervals-truncation-bounds prover/b2/truncate-intervals.lisp` shows the proof operations. The command was run on 2026-11-23.
