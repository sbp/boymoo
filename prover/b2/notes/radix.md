# Radix character accumulation

The accumulator proof inducts on the count in the radix conversion
call. The successor proof uses the character Step for the next digit and
the induction hypothesis for the recursive accumulator.

`grep -nE 'b2-radix-character-accumulator|b2-radix-digit-character' prover/b2/radix.lisp` shows the proof operations. The command was run on 2026-11-23.
