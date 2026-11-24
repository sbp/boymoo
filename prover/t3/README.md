# T3 tactics

T3 is a set of ACL2 Core books for proving recursive definition measures,
constraints, and theorems. `prover/t3/ORDER` gives the book order after the
shared `descent` book. T3 uses the `BOYMOO-PROVER` package and the `t3-`
prefix. Argument and result forms are in `sig/`. The failure convention
and the kinds used in T3 are described in `notes/failures.md`.

`(t3-api-prove statement earlier library aids)` accepts a statement line,
the earlier lines of its book, the given library, and the aid lines. A proof
is `(lemmas entry)`, with the auxiliary entry strings in dependency order
and the statement's proof string last. A statement without a proof gives
`nil`.

`(t3-api-open library)` prepares a session from the given library.
`(t3-api-prove-open session statement earlier aids)` returns the answer
and the updated session as a pair. `(t3-api-prove-all library cases)` takes
a list of `(statement earlier aids)` triples, threads one session through
the cases, and returns the answers in order.

Run the commands from the repository root.

```sh
sh prover/t3/build.sh
RUNNER=build/runner-fast/boymoo-run-fast sh prover/t3/run.sh -v
sh prover/t3/test.sh
```

The build uses the shared ACL2 launcher, the certified shared books in
`build/prover/acl2/`, and the certified exporter components in
`build/export/`. It certifies the books in `ORDER` and exports the last one
under `build/prover/t3/`. Use `sh prover/t3/build.sh BOOK` to build through a
particular book in `ORDER`.

The runner takes one canonical term per input line and writes one canonical
value per term. It uses the package declarations and program for the ACL2
library in `build/export/`. `-v` reports the load and run times on standard
error. `sh prover/t3/acl2-run.sh` evaluates the same terms with ACL2.

The test needs the driver, built with `sh prover/driver/build.sh` once
every set is built. It runs
`sh prover/driver/test.sh --sets T3 prover/t3/expected.tsv`: for each input
of `prover/t3/expected.tsv` the driver, with T3's tactics alone, writes a
proof file, and the checker in ACL2 Core and the second checker judge
it. The two must give the same verdict, and the verdict and the number
of obligations proved must be the table's. The table was recorded on
2026-11-24 with `sh prover/driver/test.sh --sets T3 --record`.
