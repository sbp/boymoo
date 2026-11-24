# Integer arithmetic proofs

Ordered additive normal forms collect equal terms. The comparison
recipes use signed tests and integer or natural-number facts about
the operands. A failed candidate can carry assumptions forward in
Evidence to the next candidate.

A Library tagged `:t3-book` supplies the rules for `NFIX` and
`SELF-NFIX`. The conditional rules use that dispatch when the arithmetic
operand contains a quoted primitive call.
