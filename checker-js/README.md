# Boymoo JavaScript checker

From the repository root, give the checker the library, statements and proofs as three files, and the library's proofs as a fourth when there are any.

```sh
sh checker-js/check.sh LIBRARY STATEMENTS PROOFS
sh checker-js/check.sh LIBRARY STATEMENTS PROOFS ENGINE
sh checker-js/check.sh LIBRARY STATEMENTS PROOFS LIBRARY-PROOFS ENGINE
```

Each file may be empty, and the forms with three or four arguments give an empty fourth input. The adapter reads the ground theory from `spec/ground.txt`. Choose an engine as the last argument or with `BOYMOO_ENGINE`; in the form with five arguments, an empty engine argument means the same as none. The default is the first of `node`, `duk`, `qjs` and `jsc` found on `PATH`. An explicit engine can be a command name or a path supplied on the command line.

Node reads bytes directly. The JavaScriptCore shell adapter uses its binary file reader. Duktape, QuickJS and other shells with `print` receive the input bytes as JavaScript string literals. The shell adapter puts its temporary files in `build/`.

Open `checker-js/index.html` from disk for the browser adapter. Select `spec/ground.txt` as the ground theory and select the other files as needed. A blank library, statements, proofs or library proofs field supplies an empty input. The page reads the selected files locally.

## Checker API

`check.js` defines `checkBoymoo(ground, library, statements, proofs, libraryProofs)` in strict ECMAScript 5.1 (ECMA-262 edition 5.1, ISO/IEC 16262:2011). Each argument is a string with one character code per file byte. The fifth argument, the library's proofs, may be left out, which gives an empty fourth input. Supply the trusted bytes of `spec/ground.txt` as the first argument. An error detected in the ground theory raises an API error. The other inputs produce a verdict whose first line follows `spec/formats.md`, section 9. A rejection includes a diagnostic on its second line.

The checker reads canonical data, admits statements, checks the eight proof rules and applies both size budgets of `spec/formats.md`. One function reads the entry of a statement and the entries that stand before it, for the proofs and for the library's proofs alike; a statement of the library is given when its entry is a `skip` or when no line of the library's proofs remains as the checker reaches it. Each call constructs its own tables. The tables have null prototypes so that decoded names can serve as keys. Integer arithmetic uses decimal limbs. Fractions and complex rationals are exact. Parsing, comparisons, term transformations and termination walks use explicit stacks or loops. A shared subterm counts at each occurrence in its logical size.

## Tests

```sh
sh checker-js/test.sh [ENGINE]
node checker-js/stress.js [ENGINE]
python3 checker-js/oracle.py [ENGINE]
```

The first command checks the example and the cases listed in [the case index](cases/README.md) against their first verdict lines, giving each case its `library-proofs.txt` as the fourth input. The stress test constructs deep terms and long lists, tests independent API calls and exercises the browser adapter with simulated file reads. The oracle compares primitive results with `checks/expected/facts.txt` and uses Python's exact fractions for additional arithmetic checks.

To check the exported books with skips, run the following commands with the engine names on `PATH`. The last two commands also take a path to the engine as an optional argument.

```sh
node checker-js/books.js node
node checker-js/books.js jsc
node checker-js/books.js duk
```

The test tool writes each book's generated proof file under `build/checker-js/skips/`. To generate skips for one export, run `node checker-js/skips.js LIBRARY STATEMENTS`. The Node run writes `build/checker-js/books.txt` in the order of `export/books.txt`. The JavaScriptCore run writes `build/checker-js/books-jsc.txt`. The Duktape run writes `build/checker-js/books-duk.txt` for 20 books sampled across the range of statement file sizes.

Each run records one library-only check and each full book check in `build/checker-js/times-ENGINE.tsv`. The per-check clock starts at entry to the checker. Wall time for the run is in `build/checker-js/summary-ENGINE.txt`. The Duktape run also records peak resident set size for each engine process.

## Recorded checks

On 2026-11-24, `sh checker-js/test.sh node` printed `all checker tests passed` on Node 22.14.0, with the example and all 390 cases; the same command with an engine of another name, which makes `check.sh` use the shell adapter, also passed. `node checker-js/stress.js` passed at 14,000 levels and 80,000 list elements. `python3 checker-js/oracle.py node` passed with 153 ACL2 values, four ACL2 refusals and 3,584 additional numeric values. `node checker-js/books.js node` checked all 460 exported books with no failure. JavaScriptCore and Duktape were not on the `PATH` and were not run on that date. The checker had 1,532 lines that are neither blank nor comment, counted with the command below.

On 2026-11-20, `sh checker-js/test.sh [ENGINE]` printed `all checker tests passed` on Node 22.14.0, JavaScriptCore and Duktape 2.7.0. All three accepted the example and agreed on all 327 cases. On the same date, `node checker-js/stress.js [ENGINE]` passed at 14,000 levels and 80,000 list elements on each engine.

On 2026-11-20, `python3 checker-js/oracle.py [ENGINE]` passed on the same three engines with 153 ACL2 values, four ACL2 refusals and 3,584 additional numeric values. `node checker-js/books.js node` and `node checker-js/books.js jsc` gave identical provisional verdicts on all 460 exported books. `node checker-js/books.js duk` matched those verdicts on its 20 sampled books.

The lines that are neither blank nor comment are counted with the following command.

```sh
awk 'NF && $1 !~ /^[\/][\/]/ {n++} END {print n}' checker-js/check.js
```

## Tools

| Tool | Used for |
|---|---|
| `node`, `duk`, `qjs`, `jsc` | The command-line hosts. Node also runs the book and stress tools. |
| A browser with local file selection and `FileReader` | The browser adapter. |
| `sh`, `cat`, `mkdir`, `mktemp`, `rm`, `od`, `awk` | The command-line adapters and case runner. |
| `python3` | The arithmetic oracle. |
| `cc` | The Duktape memory measurement on macOS or Linux. Set `BOYMOO_CC` to name another C compiler. |
