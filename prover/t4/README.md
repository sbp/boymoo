# T4 proof tactics

T4 constructs measure proofs for recursive definitions, proofs of theorems,
and witnesses for constraints. Its books use the `BOYMOO-PROVER` package
and the `t4-` name prefix. The books in `prover/t4/ORDER` follow the shared
books through `descent`. The signatures in `prover/t4/sig/` describe
the argument and result forms. The book responsibilities are in
`prover/t4/OWNERS.md`.

## Proof entry points

```lisp
(t4-api-prove statement earlier library aids)
(t4-api-open library)
(t4-api-prove-open session statement earlier aids)
(t4-api-prove-all library cases)
```

A statement is a line of text in the statement format. The library,
earlier statements, and aids are lists of lines. Aid lines supply
measures and enabled function names. Each case in `prove-all` is
`(statement earlier aids)`.

A successful answer is `(lemmas entry)`. The lemmas are auxiliary proof
strings in dependency order, and `entry` is the proof for the requested
statement. The strings include their final newlines. An
unsuccessful call gives `nil`. Internal proof operations use the
failure convention in `prover/FAILURES.md`.

`t4-api-open` prepares one library. `t4-api-prove-open` pairs its answer
with a session for the next call. `t4-api-prove-all` uses one session and
returns the answers in case order. See `prover/t4/notes/open.md` for the work
the session retains.

## Build and run

Run the commands from the repository root.

```sh
sh prover/t4/build.sh
RUNNER=build/runner-fast/boymoo-run-fast sh prover/t4/run.sh -v
sh prover/t4/test.sh
```

The build uses the certified shared books and the exporter certificates
and ground definitions in `build/export/`. It certifies the books in
`ORDER`, exports `open`, and reads back the export. Certificates and
exports are in `build/prover/t4/`. Pass a book name to `build.sh` to select
a prefix.

The runner uses the exported program and the library export. Give it
one canonical term per input line. It writes one canonical answer per
line and, with `-v`, reports load and run seconds on standard error.

The test needs the driver, built with `sh prover/driver/build.sh` once
every set is built. It runs
`sh prover/driver/test.sh --sets T4 prover/t4/expected.tsv`: for each input
of `prover/t4/expected.tsv` the driver, with T4's tactics alone, writes a
proof file, and the checker in ACL2 Core and the second checker judge
it. The two must give the same verdict, and the verdict and the number
of obligations proved must be the table's. The table was recorded on
2026-11-24 with `sh prover/driver/test.sh --sets T4 --record`.
