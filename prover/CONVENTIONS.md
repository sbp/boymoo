# The prover's books

The prover is a set of ACL2 books. They are plain ACL2: every function is in logic mode, and a runner of ACL2 Core runs them by their definitions. These rules are what lets books written by different hands fit together.

## Layout

- **The shared books**, in `prover/`, in the order of the first lines of `prover/ORDER`: `basics` (text, sequences, tables, failures), `siphash` (the hash that names a proof's helpers), `reader` (the lines of statements and proofs), `proof` and `proof2` (proof steps and the rules), `library` and `library2` (lemmas of arithmetic and of the size of lists), `termination` (the obligations of a definition) and `descent` (measures that decrease).
- **Eleven sets of tactics.** T1's books follow the shared books in `prover/ORDER` and stand in `prover/` itself. The others have a folder each (`t2`, `t3`, `t4`, `b1`, `b2`, `h1`, `h2`, `h3`, `h4`, `l1`) with an `ORDER` of its own, and stand on the shared books and on no other set.
- **The driver**, in `prover/driver/`, which stands on every set's last book.

Every book begins `(in-package "BOYMOO-PROVER")`, the package of `prover/package.lsp`.

## Names

- A function `f` of the book `m` is `m-f`; in a set's folder it carries the set's prefix first (`h4-search-run`). The functions of `basics` carry the name of what they work on: `text-`, `seq-`, `table-`, `decimal-`, `value-`, and `failure-p`.
- A constant of the book `m` is `*m-name*`.
- Each set ends in the book `open`, which gives the set's four entry functions (`prover/OPEN.md`): `SET-api-prove`, `SET-api-open`, `SET-api-prove-open`, `SET-api-prove-all`, with the set's prefix and none for T1.

## Data

- A **table** is a list of pairs `(key . value)` in the order in which the keys were first put, read with `table-get` and changed with `table-put`, a new value for a key taking the place of the old one. A set may keep a table of its own in another form (a search tree, an index) where the list is too slow, as long as what a caller can see of its order is the same.
- A **set of values** is a list without repeats.
- A **record** is `(:name field ...)`. Its owner gives a constructor and accessors and says so in the book's file under `sig/`; others use those, never the shape.
- **Nothing changes in place.** A function that would change an object takes it and returns the new one. When it also has a value to give, it returns `(cons value object)`, unless its file under `sig/` says otherwise.
- Where the absence of a value must be told from `nil`, the owner uses the keyword `:none` and says so under `sig/`.
- **Failures** are in `prover/FAILURES.md`.

## What a book may use

- The functions that are there when ACL2 starts and are in logic mode, and the functions of the books before it. No `include-book` of a book outside `prover/`. No `state`, no stobj, no array, no `hons`, no `memoize`; `defmacro` for plain abbreviation only.
- No `mv` and no `mv-let`: return a list or a pair.
- Every function is in logic mode, and ACL2 must admit it with at most a declared measure: no hint, no lemma. A recursion that has no such measure takes a counter (`prover/FAILURES.md`, "Fuel").
- No guard is verified. Each book has `(set-verify-guards-eagerness 0)` after its `in-package`, and its functions declare no guard.
- A function keeps no memory between calls. What is worth keeping across the statements of one book is carried in a session (`prover/OPEN.md`).
- **A text is walked as a list of characters.** `(coerce text 'list)` is made once, and the walk goes down that list. No loop asks a string for its length, for the character at a position or for a part of it: ACL2 defines `length`, `char` and `subseq` on a string by walking the list of its characters from the start, so such a loop takes time in proportion to the square of the text's length on a runner that runs definitions. A test of one character's code compares it with the ends of ranges instead of searching a list of codes.
- No function reads a file, a clock or the command line. The entry functions take their inputs as arguments: the statement, the earlier lines, the library and the aids, as strings and lists of strings.

## Building and testing

From the root, with ACL2 8.7:

- `sh prover/build.sh` certifies the shared books and T1's and exports the last; `sh prover/SET/build.sh` does the same for a set, and `sh prover/driver/build.sh` for the driver, once every set is built.
- `sh prover/SET/run.sh -v` (`sh prover/run.sh -v` for T1) reads one term a line and prints each value; `RUNNER` names the runner. `RUNNER=prover/tools/reference.sh` is the reference runner with its prelude, which computes `ash` and `binary-logxor`; every set runs on it.
- **The checkers judge.** `sh prover/driver/test.sh` has the driver write a proof file for each input of `prover/driver/expected.tsv`, and has the checker in ACL2 Core and the second checker judge it. The two must give the same verdict, and the verdict and the number of obligations proved must be the table's. `sh prover/SET/test.sh` (`sh prover/test.sh` for T1) is the same test with that set alone and the table `prover/SET/expected.tsv`; it needs the driver built.
- **What makes a change right.** A proof is right when both checkers accept it, whatever its text. A change to a set is right when every row of the tables still holds, or holds with more obligations proved, in which case the row is written again with `sh prover/driver/test.sh --sets SET --record`.
- ACL2 only admits the books and exports them. It never helps to find or to check a proof.
