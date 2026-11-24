# The prover

The prover of `PLAN.md`, step 6, written in ACL2 Core. It reads a library and the statements of a book, as text, and writes a proof file in the formats of `spec/formats.md`, which the two checkers judge. It is in twelve parts, each certified by ACL2 in the order of its `ORDER`: the shared books and the first set of tactics, T1, in this directory; ten more sets of tactics, in `t2/`, `t3/`, `t4/`, `b1/`, `b2/`, `h1/`, `h2/`, `h3/`, `h4/` and `l1/`; and the driver, in `driver/`, which gives each statement to the sets in turn. `DETAILS.md`, "The prover", gives the commands. [The rules of the books](CONVENTIONS.md) · [Failures](FAILURES.md) · [The entry functions of a set](OPEN.md)

## T1

T1 finds termination proofs, constraint witnesses and theorem proofs
for ACL2 Core statements. Its books run from `terms` through `open`
in `prover/ORDER`. [Book responsibilities](OWNERS.md) · [Signatures](sig/)

From the repository root, certify and export T1 with ACL2 on the
`PATH`. The build uses the exported ACL2 library under `build/export/`.

```sh
sh prover/build.sh
make -f runner-fast/Makefile
sh prover/driver/build.sh
sh prover/test.sh
```

The driver is built once every set is built (`prover/CONVENTIONS.md`,
"Building and testing"). The test runs
`sh prover/driver/test.sh --sets T1 prover/expected.tsv`: for each input of
`prover/expected.tsv` the driver, with T1's tactics alone, writes a proof
file, and the checker in ACL2 Core and the second checker judge it. The
two must give the same verdict, and the verdict and the number of
obligations proved must be the table's. The table was recorded on
2026-11-24 with `sh prover/driver/test.sh --sets T1 --record`.

To evaluate one canonical term per line, use the fast runner with
the exported theory. The `-v` option prints load and run seconds to
standard error.

```sh
RUNNER=build/runner-fast/boymoo-run-fast sh prover/run.sh -v
```

`api-open` prepares a session from the library. `api-prove-open`
returns an answer and a session for the next call. `api-prove-all`
threads one session through a list of cases.
[API signature](sig/api.md) · [Session signature](sig/open.md)
