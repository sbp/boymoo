# H1 tactics

H1 constructs proof entries for theorems, recursive definitions, and
constraints. The books in `prover/h1/ORDER` use the shared definitions
through `descent`. H1 names its functions with the `h1-` prefix.

Run these commands from the repository root.

- `sh prover/h1/build.sh` certifies the books in order and exports the last
  book. The build uses the certified shared books and exporter and
  writes certificates and exports under `build/prover/h1/`.
- `RUNNER=build/runner-fast/boymoo-run-fast sh prover/h1/run.sh -v` reads
  one canonical term per line and prints one value per term. The runner
  reports load and run seconds on standard error.
- `sh prover/h1/test.sh`, once the driver is built with
  `sh prover/driver/build.sh`, runs
  `sh prover/driver/test.sh --sets H1 prover/h1/expected.tsv`: for each input
  of the table the driver, with H1's tactics alone, writes a proof file,
  and the checker in ACL2 Core and the second checker judge it. The two
  must give the same verdict, and the verdict and the number of
  obligations proved must be the table's. The table was recorded on
  2026-11-24 with `sh prover/driver/test.sh --sets H1 --record`.

The proof entry points and session forms are specified in
`prover/h1/sig/api.md` and `prover/h1/sig/open.md`. The signatures of the
other books are under `prover/h1/sig/`. The failure kinds that guide
search are described in `prover/h1/notes/failures.md`.
