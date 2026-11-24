# B1 tactic books

B1 constructs termination, theorem, and witness certificates for ACL2
statements. Its recipes cover arithmetic, recursive data structures,
list and set operations, and constrained functions. A formula can also
be proved by search over the facts in its context.

The books use the `BOYMOO-PROVER` package. B1 functions and constants
use the `b1-` prefix. `ORDER` lists the books in dependency order.
The shared books supply the reader, proof steps, library, termination
obligations, and descent reasoning. `sig/` describes the B1 data and
calls, and `notes/failures.md` lists the failure kinds used in search.

## Proving interface

| Call | Result |
|---|---|
| `(b1-api-prove statement earlier library aids)` | The certificate for one obligation, or `nil`. |
| `(b1-api-open library)` | A session with the library prepared for proving. |
| `(b1-api-prove-open session statement earlier aids)` | A pair of the answer and the session to use for the next call. |
| `(b1-api-prove-all library cases)` | The answers in case order, using one session. |

A statement is a line string. The other inputs to `b1-api-prove` are
ordered lists of line strings. Each case for `b1-api-prove-all` is
`(statement earlier aids)`. A certificate has the form `(lemmas entry)`.
Its lemma strings are in dependency order and its entry string discharges
the obligation. Private auxiliary names include a SipHash-2-4 digest of
the canonical auxiliary text.

## Building and running

Run these commands from the repository root.

```sh
sh prover/b1/build.sh
RUNNER=build/runner-fast/boymoo-run-fast sh prover/b1/run.sh -v
sh prover/b1/test.sh
```

The build uses the certified shared books and exporter and writes B1
certificates and exports under `build/prover/b1/`. The runner reads one
canonical term per input line and writes one value per line. The
`-v` option reports load and evaluation times on standard error.

The test needs the driver, built with `sh prover/driver/build.sh` once
every set is built. It runs
`sh prover/driver/test.sh --sets B1 prover/b1/expected.tsv`: for each input
of `prover/b1/expected.tsv` the driver, with B1's tactics alone, writes a
proof file, and the checker in ACL2 Core and the second checker judge
it. The two must give the same verdict, and the verdict and the number
of obligations proved must be the table's. The table was recorded on
2026-11-24 with `sh prover/driver/test.sh --sets B1 --record`.
