# T2 tactics for ACL2 Core

T2 writes proofs for definitions, theorems, and constraints. Its tactics
construct Steps, which are justified clauses. A successful attempt returns
the proof entries for any needed lemmas followed by the entry for the
statement. The entry order is the order in which a checker can use them.

## Interface

The functions are in the `BOYMOO-PROVER` package. The arguments `library`,
`earlier`, and `aids` supply given statements, preceding statements, and
proof hints or measures. Each accepts a list of source lines, one string
containing the lines, or `nil`.

| Function | Result |
|---|---|
| `(t2-api-prove statement earlier library aids)` | `(lemmas entry)` containing proof text, or `nil`. |
| `(t2-api-open library)` | A session with the given statements admitted. |
| `(t2-api-prove-open session statement earlier aids)` | `(cons answer session2)` with the proof answer and the resulting session. |
| `(t2-api-prove-all library cases)` | The answers to the `(statement earlier aids)` cases in order, using one session. |

Each proof answer has the same form, including line terminators. Private
helper names use SipHash-2-4 of the normalized helper text. The books'
data, calls, and recovery paths are described in the
[signatures](sig/), [session notes](notes/open.md), and
[failure kinds](notes/failures.md).

## Build and test

Run the commands from the repository root.

~~~
sh prover/t2/build.sh
sh prover/driver/build.sh
sh prover/t2/test.sh
~~~

The build reads the shared `descent` certificate in `build/prover/acl2/`
and the exporter prerequisites in `build/export/`. It certifies the books
in `prover/t2/ORDER` under `build/prover/t2/acl2/` and exports the last book to
`build/prover/t2/export/`. ACL2 admits the functions into logic mode and
exports their executable terms.

The driver is built once every set is built. The test runs
`sh prover/driver/test.sh --sets T2 prover/t2/expected.tsv`: for each input
of `prover/t2/expected.tsv` the driver, with T2's tactics alone, writes a
proof file, and the checker in ACL2 Core and the second checker judge
it. The two must give the same verdict, and the verdict and the number
of obligations proved must be the table's. The table was recorded on
2026-11-24 with `sh prover/driver/test.sh --sets T2 --record`.

To evaluate canonical terms, pass one term per line to
`RUNNER=build/runner-fast/boymoo-run-fast sh prover/t2/run.sh -v`.
The runner writes each value to standard output and its load and
evaluation times to standard error. An optional book name selects an
export that was built with `sh prover/t2/build.sh BOOK`.
