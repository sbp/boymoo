# Zero from sign bounds

The zero proof combines the nonnegative and nonpositive Steps for the
same integer term. The reversed-order equality used on the nonnegative
Step rewrites the comparison inside the negated literal at `(1 1)`.

`grep -nE 'b2-powers-zero-from-signs|not-negative reversed-order' prover/b2/powers.lisp` shows the proof operations. The command was run on 2026-11-23.
