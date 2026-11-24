# H4 tactics in ACL2 Core

H4 constructs proof entries for statements in an ACL2 Core library or
book. The books in `ORDER` use the shared term, proof and library
representations. `OWNERS.md` describes each book's role. The files in
`sig/` define the argument and result forms, and `notes/failures.md`
describes the failure kinds used by the search.

## Proof interface

| Call | Result |
|---|---|
| `(h4-api-prove statement earlier library aids)` | The list `(lemmas entry)` of auxiliary entry strings and the target entry string, or `nil` if H4 gives no proof. |
| `(h4-api-open library)` | A session for the supplied library. |
| `(h4-api-prove-open session statement earlier aids)` | `(cons answer session2)` with the proof answer and the resulting session. |
| `(h4-api-prove-all library cases)` | Answers for the ordered `(statement earlier aids)` triples, using one session. |

A statement is a source string. The other inputs are ordered lists of
source lines. See `sig/api.md` for the interface and `notes/open.md` for
session preparation and reuse.

## Build and test

Run these commands from the repository root with the shared certificates,
export support and library available.

```sh
sh prover/h4/build.sh
RUNNER=build/runner-fast/boymoo-run-fast sh prover/h4/run.sh -v
sh prover/h4/test.sh
```

The build certifies the books in `ORDER` and exports the last one. Give
the build a book name to certify its prefix and export that book. H4
certificates and exports are under `build/prover/h4/acl2/` and
`build/prover/h4/export/`.

The runner reads one canonical term per input line and writes one value
per line. With `-v` it reports load and run seconds on standard error.
Specify a runner executable with `RUNNER`. The fast runner keeps compiled
functions under `build/prover/h4/cache/` by default.

The test needs the driver, built with `sh prover/driver/build.sh` once
every set is built. It runs
`sh prover/driver/test.sh --sets H4 prover/h4/expected.tsv`: for each input
of `prover/h4/expected.tsv` the driver, with H4's tactics alone, writes a
proof file, and the checker in ACL2 Core and the second checker judge
it. The two must give the same verdict, and the verdict and the number
of obligations proved must be the table's. The table was recorded on
2026-11-24 with `sh prover/driver/test.sh --sets H4 --record`.
