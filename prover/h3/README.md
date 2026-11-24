# H3 tactics

H3 produces ACL2 Core proofs for theorem, definition, and constraint
obligations. Slice tactics select a recipe by theorem name or formula
shape. Book tactics look up facts, normalize terms, and try arithmetic,
induction, measure, and witness recipes.

## Interface

The statement is one line in the interchange format. The earlier lines
are the declarations preceding that statement. The library is a list of
given declarations and the aids are a list of records for the book.
See [the interchange formats](../../spec/formats.md).

| Call | Result |
|---|---|
| `(h3-api-prove statement earlier library aids)` | `(lemmas entry)` with the proof and its local prerequisites, or `nil` if H3 gives no proof. |
| `(h3-api-open library)` | A session holding the prepared library and its fact index. |
| `(h3-api-prove-open session statement earlier aids)` | `(cons answer session)` with the answer and the updated session. |
| `(h3-api-prove-all library cases)` | The answers for a list of `(statement earlier aids)` cases in order, using one session. |

Proof entries and local prerequisites are strings with their terminating
newlines. The prerequisites appear before the entries that cite them.
See [the proof interface](sig/api.md) and [session signatures](sig/open.md).

The books use the `BOYMOO-PROVER` package and the `h3-` prefix. They
load in `ORDER` after the shared books through `descent`. The procedures
for building proof steps use the shared Library and Proof interfaces.
See [book responsibilities](OWNERS.md) and [failure handling](notes/failures.md).

## Build and test

Run the commands from the repository root. The build needs the certified
shared books and the exporter's certified books. The runner also needs
the library statements and program in `build/export/`.

```sh
sh prover/h3/build.sh
sh prover/driver/build.sh
sh prover/h3/test.sh
```

The driver is built once every set is built. The test runs
`sh prover/driver/test.sh --sets H3 prover/h3/expected.tsv`: for each input
of `prover/h3/expected.tsv` the driver, with H3's tactics alone, writes a
proof file, and the checker in ACL2 Core and the second checker judge
it. The two must give the same verdict, and the verdict and the number
of obligations proved must be the table's. The table was recorded on
2026-11-24 with `sh prover/driver/test.sh --sets H3 --record`.

To evaluate one term per input line, use the fast runner.

```sh
RUNNER=build/runner-fast/boymoo-run-fast sh prover/h3/run.sh -v
```

The runner writes values to standard output and timing to standard error.
Building the fast runner uses `make` and a C compiler. The books are
certified with ACL2.
