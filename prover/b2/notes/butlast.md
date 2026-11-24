# List truncation

A truncation record holds the index, its `NFIX` term, and the Steps
proving that term natural, integer, and nonnegative. The selector recipes
use the equality of `BUTLAST` with its corresponding `TAKE` term.

`grep -nE 'b2-butlast-truncation-(init|take-equals-butlast)' prover/b2/butlast.lisp` shows the proof operations. The command was run on 2026-11-23.
