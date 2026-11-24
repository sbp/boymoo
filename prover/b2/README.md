# B2 tactics for ACL2 Core

B2 builds proofs of recursive definitions, constrained functions, and
theorems. Its books share the reader, proof, library, and termination
operations in `prover/`. The individual interfaces are in `prover/b2/sig/`.
The book order is in `prover/b2/ORDER`.

## Proof interface

```lisp
(b2-api-prove statement earlier library aids)
(b2-api-open library)
(b2-api-prove-open session statement earlier aids)
(b2-api-prove-all library cases)
```

`statement` is one ACL2 Core statement line. `earlier`, `library`, and
`aids` are lists of lines in input order. The answer is `(lemmas entry)`
or `nil` when the tactic has no proof. The lemma strings are in dependency
order. Each lemma string and the entry string end with a line feed. A
recursive supporting definition includes its measure in the same string.

A session prepares the library for multiple proofs. `b2-api-prove-open`
returns `(cons answer session)`. Pass the returned session to the next
call. `b2-api-prove-all` takes a list of `(statement earlier aids)` cases
and returns their answers in order. The session representation is
specified in `prover/b2/notes/open.md`.

Internal proof functions follow `prover/FAILURES.md`. The conditions that
select another proof method are listed in `prover/b2/notes/failures.md`.

## Build and test

Run these commands from the repository root.

```sh
sh prover/b2/build.sh
sh prover/b2/test.sh
```

The build admits the books in order and exports `open`. The shared
`descent` certificate and the exported library supply its dependencies.

The test needs the driver, built with `sh prover/driver/build.sh` once
every set is built. It runs
`sh prover/driver/test.sh --sets B2 prover/b2/expected.tsv`: for each input
of `prover/b2/expected.tsv` the driver, with B2's tactics alone, writes a
proof file, and the checker in ACL2 Core and the second checker judge
it. The two must give the same verdict, and the verdict and the number
of obligations proved must be the table's. The table was recorded on
2026-11-24 with `sh prover/driver/test.sh --sets B2 --record`.

To evaluate canonical terms from standard input, run the following command.
The `-v` option prints load and run times to standard error.

```sh
RUNNER=build/runner-fast/boymoo-run-fast sh prover/b2/run.sh -v
```
