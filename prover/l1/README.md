# L1 tactics

L1 constructs certificates for theorem, termination, and constraint obligations. The books contain tactics for equation rewriting and structural induction, ordinal decrease, choice witnesses, and guarded or recursive application.

Every book uses the `BOYMOO-PROVER` package. `prover/l1/ORDER` gives the certification order after the shared books through `descent`. The signatures in `prover/l1/sig/` describe the argument and result forms. The failure kinds used in proof search are listed in `prover/l1/notes/failures.md`.

## Proving interface

`l1-api-prove` takes a statement line, earlier lines, library lines, and aid lines. It returns `(lemmas entry)` for a certificate or `nil` when it has no certificate. The returned strings include their line terminators.

`l1-api-open` prepares a library for repeated calls. `l1-api-prove-open` returns an answer paired with the session for the next call. `l1-api-prove-all` passes one session through a list of cases and returns their answers in order.

## Build and test

Run the commands from the repository root.

```sh
sh prover/l1/build.sh
sh prover/l1/test.sh
```

The build uses the certified shared books under `build/prover/acl2/` and the exporter prerequisites under `build/export/`. It puts the L1 certificates in `build/prover/l1/acl2/` and the exported program in `build/prover/l1/export/`. An optional book name limits certification to that book and its predecessors.

The test needs the driver, built with `sh prover/driver/build.sh` once every set is built. It runs `sh prover/driver/test.sh --sets L1 prover/l1/expected.tsv`: for each input of `prover/l1/expected.tsv` the driver, with L1's tactics alone, writes a proof file, and the checker in ACL2 Core and the second checker judge it. The two must give the same verdict, and the verdict and the number of obligations proved must be the table's. The table was recorded on 2026-11-24 with `sh prover/driver/test.sh --sets L1 --record`.

To evaluate terms directly, give the runner one canonical term per line on standard input. The values go to standard output. With `-v`, the runner also reports loading and evaluation times on standard error.

```sh
RUNNER=build/runner-fast/boymoo-run-fast sh prover/l1/run.sh -v
```
