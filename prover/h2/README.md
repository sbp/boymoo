# H2 tactic books

H2 constructs certificates for definitions, constraints, and theorems in
the canonical input format in `spec/formats.md`. The books use ACL2
Core in the *BOYMOO-PROVER* package and load in the order of [ORDER](ORDER).
The [book responsibilities](OWNERS.md) and [signatures](sig/) describe
the search operations and their data.

- `(h2-api-prove statement earlier library aids)` proves one statement.
- `(h2-api-open library)` prepares a session for the library.
- `(h2-api-prove-open session statement earlier aids)` returns a pair of
  the answer and the updated session.
- `(h2-api-prove-all library cases)` runs the cases in order in one
  session. Each case is a list of the statement, earlier lines, and aids.

A certificate is `(lemmas entry)`, with a list of auxiliary entry strings
in dependency order and the proof entry string for the statement. Each
string ends with a newline. The proving calls give `nil` when they have
no certificate. The [session signature](sig/open.md) describes what a
session retains between calls.

Run these commands from the repository root.

```sh
sh prover/h2/build.sh
RUNNER=build/runner-fast/boymoo-run-fast sh prover/h2/run.sh -v
sh prover/h2/test.sh
```

The build certifies the books and exports `open`. The run command reads
one canonical call per line and writes one result per line. With `-v`
it reports load and evaluation times on standard error. The test is `sh prover/driver/test.sh --sets H2 prover/h2/expected.tsv`:
for each input of `prover/h2/expected.tsv` the driver, with H2's tactics
alone, writes a proof file, and the checker in ACL2 Core and the second
checker judge it. The two must give the same verdict, and the verdict and
the number of obligations proved must be the table's.
[DETAILS.md](DETAILS.md) lists the tools and inputs.
