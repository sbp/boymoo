# Measure candidates

A selector-chain proof combines strict bounds for individual selector
edges and carries the resulting ruler evidence. The measure dispatcher
tries candidates in plan order and carries the resulting Library to a
subsequent candidate when the failure permits another trial.

`grep -nE 'b2-measures-(selector-chain|plan-attempt|try-plans)' prover/b2/measures.lisp` shows the proof operations. The command was run on 2026-11-23.
