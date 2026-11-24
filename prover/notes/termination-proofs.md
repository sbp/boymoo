# Termination proof obligations

Termination proofs establish ordinality and decrease for the chosen
measure. Decrease combines the proofs of the recursive calls with the
rulers of their branches. Equal clauses can reuse a proof step, and a
proof with fewer side literals can cover a stronger branch.

Optional descent and ordinality tactics receive requests containing
the current library. A descent reply can include Rulers with the
hypotheses it established. The signatures give the request and reply
forms. See `prover/sig/termination-proofs.md`.
