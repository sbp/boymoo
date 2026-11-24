# Book dependencies

The arithmetic, truncation, product, record, reversal, sorting, and
strict order books declare recipe events. `tactics` admits those events
after defining the proof functions that the recipes call. `prover/b2/ORDER`
places the remaining books after their dependencies.

`grep -nE declare-events prover/b2/tactics.lisp` shows the proof operations. The command was run on 2026-11-23.
