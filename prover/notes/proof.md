# Proofs and proof steps

The signatures are in `prover/sig/proof.md`.

## A Step is a value

A Step holds its premises, so it is the whole proof of its clause, and two Steps with the same word, data and clause are the same Step wherever they were made. `proof-serialize` relies on that: it keeps a table from each Step to the number of its line, so a subproof that occurs twice is written once, and it also writes one line for two Steps that differ and give the same line. `lemmas-slice-library-share-proofs` of `prover/lemmas.lisp` finds a proof that several obligations repeat in the same way, by `equal`.

Nothing in a Step says which Proof it was made in. A rule reads the facts and the primitives of the Proof it is given, and the caller keeps Steps and Proof together.

## The ground theory

`proof-proof-init` returns the constant `*proof-ground*`, which the book computes when it is loaded from the records of `spec/ground.txt` written into the book: 32 `primitive`, 37 `define` and 144 `clause`. A change to `spec/ground.txt` has to be made in the book as well. On 2026-11-23 the two agreed in number: `grep -c '^(clause ' spec/ground.txt` and `grep -c '^     ("clause" ' prover/proof.lisp` both gave 144, and the same two commands for `define` and `primitive` gave 37 and 32.

The `package` and `specials` lines of `spec/ground.txt` have no record in the book.

## The rules and the checker

The word and data of a Step are what its line says in a proof file (`spec/formats.md`, section 6), so the eight rules of the book are the eight step lines. The rules make only Steps that their own tests allow, but they are not the judge: a proof is accepted when a checker accepts the text that `proof-proof-entry` writes.

`proof-proof-compute` is the one rule that takes its conclusion on trust. The line `(compute TERM)` carries the term alone, the caller supplies the value for the clause of the Step, and a checker computes the value again.

`proof-proof-instantiate`, `proof-proof-subsume`, `proof-proof-tidy` and `proof-proof-front` return the Step they were given when there is nothing to do, so a proof has no step that changes nothing.

## Kinds

The kind of a Proof, `:base`, `:slice` or `:book`, is its fifth member, and a Proof of the kind `:base` has only four. `proof-proof-with-facts` and `proof-proof-add-definition` keep the kind. `prover/sig/proof2.md` says what the kind chooses.

## Places

A place in a Step counts literals and arguments from 1, as the line `(substitute P Q I J1 ... Jk)` does. `(1)` is the first literal, `(1 2)` the second argument of the first literal, the right side when that literal is an equality.
