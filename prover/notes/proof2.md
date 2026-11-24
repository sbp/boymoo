# Derived proof rules

The signatures are in `prover/sig/proof2.md`.

## Why the kind is read from the Proof

The rules of this book call one another. `proof-proof-symmetric` and the simplifier call `proof-proof-reflexive`, the simplifier and so `proof-proof-prove` call `proof-proof-constant`, and the count lemmas of `prover/library2.lisp` call `proof-proof-by-value`. A set whose Library proves reflexivity by its own lemma, or computes more constants, needs that form in those inner calls as well as in its own. So the three rules read the kind from the Proof at each call, and a caller chooses once, when it makes the Proof.

`proof-proof-reflexive-base` and `proof-proof-constant-base` are for the caller that wants the `:base` form whatever the kind. The slice build uses the first to prove the lemma `SELF-EQUALITY-REFLEXIVE` that the kind `:slice` then cites (`prover/lemmas.lisp`).

The lemmas `SELF-EXCLUDED-MIDDLE`, `SELF-IF-FALSE` and `SELF-IF-TRUE` are different: `proof-proof-assume`, `proof-proof-if-false` and `proof-proof-if-true` cite them in a Proof of any kind as soon as it has them, and prove the same clause from the ground theory before. `library-library-logic-and-types` adds the three before any other lemma, so the proofs after them cite the lemmas and do not prove the clauses again.

## Side literals

A rule of this book returns a Step whose first literal is its conclusion and whose side literals are the assumptions still open. `proof-proof-assume` opens one: its Step has the term and, as its side literal, the negation. `proof-proof-cases` closes a pair, and `proof-proof-discharge` closes one against evidence. A lemma is added with the side literals that are left (`library-library-lemma`).

## Counters

The walk of a value, the simplifier and the prover each take a counter that begins at 1,000,000 and return a failure of the kind `"Fuel"` at 0. The failure names the function that ran out.

## Shared with later books

`proof-with-checked-results`, `proof-term-at` and `proof-list-of-length` are how a book reads a term that may lack a member and passes a failure on. The parts of the simplifier and of the prover that `prover/sig/proof2.md` lists are called by books of the sets that have a simplifier or a prover of their own and take single moves from this one.

`proof-proof-discharge` is `proof-discharge` of `prover/proof.lisp` under the name of a rule.
