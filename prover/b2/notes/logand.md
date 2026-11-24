# Bounds for bitwise conjunction

The bitwise conjunction bounds use strict and weak comparisons derived
from the recursive operands. The bounds helper returns the lemma name
and its Library. The named theorem recipe instantiates that lemma.

`grep -nE 'b2-logand-(logand-bounds|prove-logand) ' prover/b2/logand.lisp` shows the proof operations. The command was run on 2026-11-23.
