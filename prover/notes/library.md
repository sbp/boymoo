# The library of lemmas

The signatures are in `prover/sig/library.md`.

## A Library is a Proof and what was added to it

The entries of a Library are the text that a proof file needs before it can cite the Library's lemmas: each lemma with its proof, each definition, in the order of adding. A tactic that proves a statement with the Library returns the entries that its proof needs together with the entry of the statement (`prover/OPEN.md`).

A lemma is named without its prefix. `library-library-lemma` and `library-library-cite` take `"LESS-SHIFT"`, and the fact, the head line and every citation in a proof file have `ACL2::SELF-LESS-SHIFT`. `library-lemma-name` gives the symbol. The axioms of ACL2 keep their own names, as symbols of `ACL2`, and are cited by `library-library-axiom`; the facts of the ground theory that have strings for names are cited by `proof-proof-fact`.

`library-library-lemma` returns a failure, and no Library, when the name is taken. The caller still has the Library that it passed.

## Types

`library-library-type-of` and `library-library-natural` add nothing to the Library: they cite lemmas that the build has added and return a Step. `library-library-type-of` knows an integer constant, a sum, a product, a negation, and a call of `ACL2-COUNT` or `LEN`; the type of any other term has to be in the evidence. The sets that prove the type of more terms, and add a lemma for it when they first need it, have functions of their own that return the Library with the Step (`descent-library-type-of` in `prover/sig/descent.md`, `lemmas-slice-library-type-of` in `prover/sig/lemmas.md`).

`library-type-evidence` is the first thing that `library-library-type-of` does, and `descent-library-type-of` likewise: a Step of the evidence that already proves the type is taken as it is.

## Sums

`library-library-linear-form` takes its types from `library-library-type-of`, so it too leaves the Library as it is. A book that needs the normal form of a sum over terms whose types add lemmas makes it from the same parts with its own types: `library-linear-reassociate`, `library-linear-sort` and `library-linear-combine-pair` are called so by `prover/countdowns.lisp`, `prover/proof-search.lisp` and books of the sets.

The order of the terms of a normal form is by their texts as `proof-write` gives them, so it is the same wherever the sum is normalized, and two sums are equal when their normal forms are the same term (`library-library-linear-equal`).

The recursions on sums take a counter that begins at 1,000,000 (`prover/FAILURES.md`).

## The order of the lemmas

`library-library-logic-and-types` comes first and `library-library-additive-identities` second: the identities cite `INTEGER-SUM` and `INTEGER-NEGATION` for the types of their sums, and the rules of sums cite `ADD-ZERO-LEFT`, `ADD-ZERO-RIGHT` and `ADD-SWAP`, which the identities add first. `library-library-push-minus` looks for `DOUBLE-NEGATION` and `NEGATE-SUM` among the facts and leaves a negation where it is while they are not there, which is how the identities can prove `NEGATE-SUM` with the rules of sums before the Library has it. The rest of the build is in `prover/sig/library2.md`.
