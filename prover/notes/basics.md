# Text, sequences and tables

The signatures are in `prover/sig/basics.md`.

A table keeps the order in which its keys were first put. `table-put` on a key that is there changes the value in its place, and `table-update` is `table-put` of each entry in turn, so the keys that the second table brings come after those of the first.

`seq-sorted` is a sort by insertion, and members that `value-less` does not order keep the order they came in. `proof-proof-init` sorts the primitives of the ground theory with it.

Two functions split a text into lines. `text-lines` ends a line at any character of code 10 to 13 or 28 to 30; `api-as-lines` of `prover/api.lisp` uses it when lines are given as one string. `run-split-byte-lines` of `prover/book-proofs.lisp` ends a line only at a line feed, at a return, and at a return with a line feed after it, and is the one for the text of a proof.

`text-quoted` is there for the messages of failures: `prover/proof.lisp` and `prover/library.lisp` write the texts in their messages with it. The failures of `seq-index` and `table-delete` have an empty message. `prover/FAILURES.md` says which kinds of failure a caller may still tell apart.

The failures of this book are of the kinds `"value"`, from `text-split`, `text-split-max`, `seq-range` and `seq-index`, and `"key"`, from `table-delete`. No recursion in it can run out of its counter: `text-split-max` counts down from the length of the text, and `decimal-text` from 9 for each digit.
