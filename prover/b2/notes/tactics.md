# Tactic requests

Case, implication, and induction tactics use requests for branch
proofs. A reply carries the Step and its Library. The induction scheme
combines the base and advancing cases and uses the evidence and measure
comparison supplied by its caller.

`grep -nE 'b2-tactics-(choose|tactics-implication|tactics-by-induction|tactics-on-list)' prover/b2/tactics.lisp` shows the proof operations. The command was run on 2026-11-23.
