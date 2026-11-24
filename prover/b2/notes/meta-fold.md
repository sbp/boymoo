# Arithmetic fold dispatch

The fold dispatch table maps evaluator tags to constraint symbols in
insertion order. A constraint index is a signed decimal integer with
optional surrounding whitespace. Underscores may separate digits. The
index parser accepts up to 4,300 digits.

`grep -nE 'b2-meta-fold-(constraint-index|arithmetic-fold-init-dispatch)|4300' prover/b2/meta-fold.lisp` shows the proof operations. The command was run on 2026-11-23.
