# The prover

The prover of `PLAN.md`, step 6, written in ACL2 Core. It reads a library and the statements of a book, as text, and writes a proof file in the formats of `spec/formats.md`, which the two checkers judge. It is in twelve parts, each certified by ACL2 in the order of its `ORDER`: the shared books and the first set of tactics, T1, in this directory; ten more sets of tactics, in `t2/`, `t3/`, `t4/`, `b1/`, `b2/`, `h1/`, `h2/`, `h3/`, `h4/` and `l1/`; and the driver, in `driver/`, which gives each statement to the sets in turn. `DETAILS.md`, "The prover", gives the commands. [The rules of the books](CONVENTIONS.md) · [Failures](FAILURES.md) · [The entry functions of a set](OPEN.md)

## Executable driver

From the repository root, after building and exporting the prover with
`sh prover/build-all.sh`, run `sh compiler/build-prover.sh`. It certifies
and exports the entry, then compiles it and the definitions reached by
its calls to `build/compiler/prover`. The program uses the same tactic
definitions as the fast runner. Set `PROVER_HEAP_LIMIT` at build time
to choose the copying space size in MiB. The default is 1024. Each run
has the heap limit built into its executable. By default the compiler,
`build/compiler/compiler-2`, compiles the prover; set `COMPILER` to
another compiled compiler to compile it with that one. The executable is
`build/compiler/prover` either way. See `compiler/README.md` for the exit
statuses and the memory of the executables that the compiler writes.

```sh
PROVER_DRIVER=compiled sh prover/driver/prove.sh [--sets A,B] [--ranks N] [--checked] LIBRARY STATEMENTS [AIDS]
```

The script writes six fields to the executable using `compiler/frame.sh`.
The fields are the ground theory when `--checked` is given, the library,
the statements, the aids, the comma-separated tactic names and the
decimal rank limit, in that order. An absent field is empty. Each field
begins with its byte length as four bytes, the most significant first.
The executable writes the proof file directly, including a skip entry for
each obligation it leaves unproved. A malformed frame, a driver failure or
a rejected proof with `--checked` exits with status 1. The default driver
is the fast runner.

`sh prover/test-all.sh --compare` gives each case in the driver's and
tactics' tables to both drivers, compares the proof bytes and checks the
compiled driver's proof. The logs under `build/prover/compare/` give the
comparison and any driver stops for each table. `PROVER_TEST_JOBS` sets
the number of concurrent table tests, and `PROVER_TEST_SECONDS` bounds
each proof attempt in comparison mode (240 seconds by default).

On 2026-11-27, with the prover that the compiler writes,
`PROVER_TEST_JOBS=1 sh prover/test-all.sh --compare` printed
`All prover tests passed.` `compiler/README.md`, "Results", gives the
time and memory of the compiled prover on five books.

## Library and books

```sh
PROVER_DRIVER=compiled sh prover/library.sh -j 2 -f build/prover/library-compiled.proofs
sh compiler/build-checker.sh
PROVER_DRIVER=compiled NODE_OPTIONS=--max-old-space-size=1024 \
    sh prover/books.sh -j 3 -t 120 -l build/prover/library-compiled.proofs --all
```

The library command stores attempts under `build/prover/library-compiled/`
with the compiled driver and `build/prover/library/` with the fast runner.
The book command with `--all` reads the names in `export/books.txt`.
Omit `-l` to run the library command first. The compiled driver mode
uses the compiled ACL2 Core checker and the JavaScript checker. A book
can appear in the accepted list only with an `accepted` verdict from
each. For other books the report gives the verdicts and names the
obligations left as skips, or gives the reason a run stopped.

`-j JOBS` controls the number of books processed at once. `-t SECONDS`
sets the time limit for each driver or checker invocation, 600 seconds
by default with `--all`. `PROVER_DRIVER=compiled sh prover/books.sh
--summary` prints the available results of the compiled driver's
all-book run, with pending books identified. Proofs and individual
results from that run are under `build/prover/books-compiled/all/`.

### Library result

On 2026-11-26, the library command above took 5572.72 seconds, with a
maximum resident memory of 2277408 KiB measured with the `time` of
`zsh`. It printed
`873 of 873 obligations of the library proved; 0 left as skips; 161628902 bytes in build/prover/library-compiled.proofs`.
The pieces spanning lines 1790–1809, 1810–1829, 1830–1849 and 1850–1862
of the library's statements reached the heap limit. Of 73 individual
retries, 38 proved their obligation and 35 reached the heap limit.
L1 alone proved those 35 warrant theorems. Every attempt finished
within its time limit. The attempt record for this run is
`build/prover/compiled-check/library-attempts.tsv`.

```sh
cmp build/prover/library.proofs build/prover/library-compiled.proofs
: > build/empty
sh compiler/check.sh build/export/library.statements build/empty build/empty build/prover/library-compiled.proofs
NODE_OPTIONS=--max-old-space-size=1024 sh checker-js/check.sh build/export/library.statements build/empty build/empty build/prover/library-compiled.proofs node
```

On 2026-11-26, `cmp` found the proof files byte-for-byte identical.
Both checkers printed `accepted`. The compiled checker took 25.08
seconds and 344032 KiB maximum resident memory. The JavaScript checker
took 12.85 seconds and 505760 KiB.

### Book result

On 2026-11-26, `PROVER_DRIVER=compiled sh prover/books.sh --summary`
printed the summary below for the all-book command above.
The sweep took 17647.36 seconds with a maximum resident memory of
2107248 KiB, measured with the `time` of `zsh`.

Both checkers gave the same verdict on each of the 265 books they judged.
They accepted 254 in full and reported 26 skipped obligations across 11
books. The driver reached the time limit on 194 books and the heap
limit on `system/apply/apply-prim`.

The books with skipped obligations, which both checkers judged
provisional, are these:

| Book | Skipped obligations |
|---|---:|
| `misc/hidden-defpkg-checks/top` | 1 |
| `build/choice` | 1 |
| `arithmetic/equalities` | 2 |
| `system/pseudo-good-worldp` | 3 |
| `arithmetic-3/bind-free/integerp-meta` | 2 |
| `arithmetic-3/bind-free/normalize` | 3 |
| `arithmetic-5/lib/basic-ops/common` | 2 |
| `arithmetic-5/lib/basic-ops/integerp-meta` | 5 |
| `arithmetic-5/lib/basic-ops/natp-posp` | 4 |
| `arithmetic-5/lib/floor-mod/logand-helper` | 2 |
| `misc/hidden-defpkg-checks/sub2` | 1 |

`PROVER_DRIVER=compiled sh prover/books.sh --summary` prints the full
report from the records under `build/prover/compiled-check/`: the books
accepted in full, and for each other book what is left.

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
