# Boymoo

Boymoo is an independent checker for the [ACL2](https://www.cs.utexas.edu/~moore/acl2/) theorem prover. It has two goals.

1. **A checker small enough to audit.** It accepts a theorem only with a proof written out in primitive steps, and it does not rest on ACL2's own word that the theorem is proved.
2. **Durability.** A proof can be checked with a small stack of software that contains neither ACL2 nor Common Lisp.

Its watchwords are that it be auditable, minimal and efficient, and that it reuse as much existing ACL2 work as it can: every book that ACL2 can load is to become input for it.

## How it works

ACL2 is the front end. It reads a book, expands every macro, and writes what the book states as plain **statements**: definitions, theorems, axioms, functions introduced by constraint or by choice, and packages. What remains of ACL2's language after that expansion is small: seven kinds of data, 32 primitive functions, terms, and eight kinds of statement. This repository calls it **ACL2 Core**. ACL2's documentation names the parts, translated terms and primitive event macros; the name for the whole is this project's.

ACL2 is the definition of ACL2. Wherever ACL2 decides something, by its axioms, by its evaluator or by the tests it makes before it admits an event, ACL2 Core decides the same, and a check confirms it against ACL2.

A **checker** reads four things: a library of statements that are taken as given unless the fourth proves them, the statements of a book, a file of proofs, and a file of proofs of statements of the library, which may be empty. It answers with one line:

- `accepted`: every theorem follows, by eight rules of inference, from ACL2's axioms and the library's and the book's own statements, and every statement of the library that calls for a proof is proved;
- `provisional`, with four counts: the same, except for the proofs that were skipped, the axioms that were assumed, and the definitions and facts of the library that were given;
- `rejected`, with the place of the first line that fails.

ACL2 says what a book states and is used to cross-check. It takes no part in finding or checking a proof.

## What is in the repository

The repository holds the specification, the checks that compare it with ACL2, the exporter, by which ACL2 writes its library and its books in the formats, the reference runner, which computes the value of a term from program text, a checker written in ACL2 Core, which the runner runs, a second checker, written apart from it in JavaScript, the prover, in ACL2 Core, which writes proofs for the checkers to judge, and the compiler, in ACL2 Core, which turns ACL2 Core programs into executables for aarch64. [`PLAN.md`](PLAN.md) gives the order of the work.

| Path | What it is |
|---|---|
| [`spec/language.md`](spec/language.md) | The language: data, the 32 primitive functions and their value on every input, running and attachments, terms, names, the eight kinds of statement, and what each kind of ACL2 event becomes. |
| [`spec/logic.md`](spec/logic.md) | The logic: the axioms, the eight rules with the argument that each is sound, how each statement is admitted and what must be proved for it, what a verdict means, with the argument for it, and the facts beyond ACL2's axioms that ACL2 itself reasons with. |
| [`EDGE-CASES.md`](EDGE-CASES.md) | Every place found where what ACL2 does goes beyond, falls short of or differs from what its axioms say, with an example of each that the checks run, what ACL2 Core does there, and why where it does not follow ACL2. |
| [`spec/formats.md`](spec/formats.md) | The interchange formats: the text of data, statements and proofs, the order of checking, the budgets, and the three verdict lines. |
| [`spec/ground.txt`](spec/ground.txt) | The ground theory that every checker holds: ACL2's packages, primitives and axioms, the definitions they mention, and the clauses about `acl2-count` that ACL2's prover has built in, as data. ACL2 writes it. |
| [`spec/example/`](spec/example) | One theorem and its proof in seven steps, in the formats. |
| [`checks/`](checks) | The checks: scripts and four small books for ACL2, the printer of the formats (`canon.lisp`, a book, which every script that prints loads through `canon.lsp`), a reader for the formats, the expected results, and `run.sh`, which runs them all. |
| [`export/`](export) | The exporter: a program run by ACL2 that writes its built-in library and its books as statements, program text and the prover's aids, split into a core with no state, an ACL2 book in logic mode with its guards declared (`core.lisp`), and a shell that reads the session and writes the files (`export.lsp`); a check by which ACL2 reads each file back (`readback.lsp`); the books chosen (`books.txt`) with a small book of two cases of its own (`choice.lisp`); `certify.sh`, which has ACL2 certify the printer and the core, and, with `--guards`, the books that verify the core's guards; `run.sh`, which runs it all; and `prove.sh`, which runs every proof about it. `README.md` there describes the core: its entry functions, what each takes and returns, and what lies outside it. |
| [`export/proofs/`](export/proofs) | The proofs of `PLAN.md`, step 4b, about the core and the printer: ACL2 books in five sets, `round-trip` (the printer and the checker's reader), `guards` (the guards of the core), `structure` (completeness without repeats, and order), `well-formed` and `faithful`. Each set has a script, `NAME.sh`, which certifies its books and tests the hypotheses of its theorems on ACL2's worlds, with the tests it loads, and a report, `NAME.md`, which gives every theorem with its hypotheses, their tests, and what the theorem does not say. |
| [`runner/`](runner) | The reference runner: a program in ISO C99 that reads program text and computes the value of a term (`runner/README.md`), with the functions of its prelude on strings and lists in `prelude.c`, which the fast runner compiles too, its `Makefile`, its tests against ACL2 (`test.sh`, with the files of `runner/test/`), its benchmarks against ACL2 (`bench.sh`, with the books of `runner/bench/`), and the timing of its prelude (`prelude.sh`). |
| [`runner-fast/`](runner-fast) | The fast runner, a tool for development that nothing trusts: the reference runner with the definitions a run needs translated into C, compiled and loaded, which must give the reference runner's output and status (`runner-fast/README.md`); its `Makefile`, its test against the reference runner (`test.sh`, with, in `runner-fast/test/`, the generator of its calls, ACL2's values for two sets of them, and the script that records those values), and its benchmarks against it (`bench.sh`). |
| [`checker/`](checker) | The checker of `spec/logic.md`, in ACL2 Core: six ACL2 books in the package of `package.lsp`, which read the four inputs as strings and give the verdict (`base.lisp`, `read.lisp`, `terms.lisp`, `rules.lisp`, `admit.lisp`, `check.lisp`); `build.sh`, which has ACL2 certify them and the exporter export them, and writes the checker's library, the lines of ACL2's library that it calls, with `library.awk`; `check.sh`, which runs the checker on the runner, with the shell functions of `quote.sh`; `acl2-check.sh`, with `acl2-run.lsp`, which runs the same functions inside ACL2; its tests, `test.sh`, with the cases of `checker/cases/` and the tools `closed.py` and `skips.py`; `books.sh`, which runs it on the books of `export/books.txt`; `size.sh`; and `checker/proofs/`, 15 ACL2 books that verify the guards of its functions, with `guards.sh`, which certifies them and checks their certificates, and `guards.md`, which gives the guards and what they show. |
| [`checker-js/`](checker-js) | The second checker of `PLAN.md`, step 4, written from the specification alone in ECMAScript 5.1 (`check.js`), with adapters for several JavaScript engines and a browser, its cases (`checker-js/cases/`), its tests and its tools; [`checker-js/README.md`](checker-js/README.md) gives its commands. |
| [`review/`](review) | The review of `PLAN.md`, step 5: `review/steps/`, the book of steps, by which ACL2 certifies the conclusion of each step of the proofs of the checker's cases and of its proofs of its own termination; `review/termination/`, the comparison of the obligations of termination that the checker computes with ACL2's measure conjectures; and `review/self/`, which writes the proofs of termination of the checker's own definitions in the formats and has both checkers check them. The README of each says what it does and what it shows. |
| [`prover/`](prover) | The prover of `PLAN.md`, step 6, in ACL2 Core: 458 ACL2 books in the package of `package.lsp`, in twelve parts, each with its `ORDER`, `build.sh`, `run.sh` and documents: the shared books and the first set of tactics, T1, at the top; ten more sets of tactics, `t2/`, `t3/`, `t4/`, `b1/`, `b2/`, `h1/`, `h2/`, `h3/`, `h4/` and `l1/`, each with a `test.sh` and its table `expected.tsv`; and `driver/`, which gives each statement to the sets in turn and writes the proof file; `build-all.sh` and `test-all.sh`, which build and test it all; `library.sh`, which proves the library and writes the library's proofs; and `books.sh`, which proves books and has both checkers judge them with those proofs. [`prover/README.md`](prover/README.md), [`prover/CONVENTIONS.md`](prover/CONVENTIONS.md), [`prover/FAILURES.md`](prover/FAILURES.md), [`prover/OPEN.md`](prover/OPEN.md) and [`prover/OWNERS.md`](prover/OWNERS.md) give the overview, the rules of the books, the failure values, the entry functions of a set and what each book is responsible for; each book has its signatures under `sig/`. |
| [`compiler/`](compiler) | The compiler of `PLAN.md`, step 7, in ACL2 Core: ten ACL2 books in the package of `package.lsp`, which turn ACL2 Core program text into an executable for aarch64, for macOS or for Linux, and write every byte of it with no assembler, linker or library (`read.lisp`, `index.lisp`, `data.lisp`, `gen.lisp`, `a64.lisp`, `runtime.lisp`, `sha256.lisp`, `macos.lisp`, `linux.lisp`, `compile.lisp`); `checker-entry.lisp`, the entry of the compiled checker, with `build-checker.sh`, which builds it, `check.sh`, which runs it on four files as `checker/check.sh` runs the checker on the reference runner, and `frame.sh`, which writes its input; `build.sh`, which has ACL2 certify the books and the exporter export them; `compile.sh`, which compiles on the reference runner, with the decoder of `decode.sh`; `bootstrap.sh`, which has the reference runner compile the compiler and the result compile it again; its tests, `test-front.sh`, `test-a64.sh`, `test-numbers.sh`, `test-symbols.sh`, `test-targets.sh` and `test-checker.sh`; and `compiler/model/`, models in ACL2 of ACL2 Core and of the A64 machine, with their tests. [`compiler/README.md`](compiler/README.md) and [`compiler/model/README.md`](compiler/model/README.md) give the design and the commands. |
| [`LICENSE`](LICENSE) | The licence. |
| [`PLAN.md`](PLAN.md) | The steps of the work, what each gains, and how each is judged finished. |
| [`AGENTS.md`](AGENTS.md) | The rules that bind every change to this repository. |

A reader new to the project should read `spec/language.md`, then sections 1, 5, 6, 9 and 10 of `spec/logic.md`, then `spec/formats.md`, and then `EDGE-CASES.md` for where ACL2 and its axioms part.

## Tools

Every tool is found by its name on the `PATH`.

| Tool | Used for |
|---|---|
| `acl2` | ACL2 version 8.7, with the books that are distributed with it, of which `projects/apply/top` must be certified. The checks ask ACL2 what it holds, have it prove the facts that the specification adds to its axioms, and have it certify three small books of their own in `build/`. The checks and the exporter run under this version only: they read properties of ACL2's world, which can change from one version to the next without notice, so that another version could give a wrong answer and report no error. ACL2 loads [`checks/version.lsp`](checks/version.lsp), the one place that names the version, at the start of the first run of `checks/run.sh` and of every run of `export/book.sh` and `export/certify.sh`; under any other version it ends at once, and the script prints the version it found and stops with status 3. |
| `python3` | Python 3.5 or later, for `checks/reader.py`, the reader of the formats, `export/measure.py`, which counts and measures what the exporter writes, the files of `runner/test/` that write the reference runner's test cases, and the test tools `checker/closed.py` and `checker/skips.py`; Python 3.8 or later for the scripts of `review/`. |
| `make`, `c99` | The `make` and the C compiler of POSIX, to build the runner (`runner/Makefile`); the compiler may be named otherwise with `CC`. Nothing else is needed to build or run the runner. |
| `cc` | For the fast runner (`runner-fast/README.md`), a C compiler, found as `cc` both to build it (`runner-fast/Makefile`, where it may be named otherwise with `CC`) and when it runs, to compile the C it writes. It must accept the options `-O2`, `-w`, `-fPIC`, `-I` and `-c`, and `-dynamiclib -undefined dynamic_lookup` to link a shared library, and support `__int128`, `__builtin_frame_address` and `__attribute__((musttail))`; the system must provide POSIX threads, `posix_spawn` and `dlopen`. Apple clang on macOS does both. Nothing else of the repository needs it. |
| `sh`, `cmp`, `cp`, `grep`, `sed`, `tr`, `paste`, `rm`, `mkdir`, `date`, `cat` | The usual POSIX tools, for `checks/run.sh`, `export/run.sh` and `export/prove.sh`. |
| `timeout`, `xargs` | `timeout` also bounds the runs of ACL2 and of the runner in the scripts of `prover/`. For `export/run.sh`: `timeout` (of GNU coreutils) stops a run of ACL2 on one book after 30 minutes, and `xargs`, with its option `-P`, runs two at a time. `export/prove.sh` uses `timeout` too, with `awk`, and `review/termination/run.sh` uses both as `export/run.sh` does, with `sort` and `comm`. |
| `awk`, `env`, `time`, `sort`, `paste`, `head`, `cut`, `mv`, `cksum` | The POSIX tools that `runner/test.sh`, `runner/bench.sh` and `runner/prelude.sh` use besides those above; `runner-fast/test.sh` and `runner-fast/bench.sh` use the same, and `cksum` is for `runner-fast/test.sh` and `runner-fast/test/record.sh` alone. |
| `node`, or `duk`, `qjs`, `jsc` | A JavaScript engine, for the second checker (`checker-js/README.md`); `checks/agree.sh` uses `node` unless another is named, and `node` for the tool that writes the second checker's skips; `review/steps/run.sh` and `review/self/run.sh` use `node`. |
| `clang`, `otool`, `codesign` | On macOS, for the compiler's tests alone, which check what the compiler writes and take no part in making it: `compiler/test-a64.sh` assembles A64 instructions with `clang -arch arm64 -c` and reads the object's text section with `otool -s __TEXT __text`, to compare the compiler's encodings with the system assembler's, and `compiler/test-targets.sh` checks the signature that the compiler writes with `codesign -v --strict`. |
| `docker`, `colima`, `tar` | Optional, for `compiler/test-targets.sh`: when `docker` reaches a running Colima, the script archives the Linux executable that it compiled with `tar`, makes a local image that holds only that executable with `docker import`, runs it with no network, and removes the image; with no such Colima it says so and skips that run. |
| `zsh`, `fold`, `chmod`, `mktemp` | For the scripts of `compiler/`, besides tools named in other rows: `compiler/test-checker.sh` times each run, and measures its peak of resident memory, with the `time` of `zsh`; `compiler/decode.sh` divides the string that the reference runner prints into lines of bounded length with `fold`, for `awk`; `chmod` makes executable the files that the compiler writes; and `mktemp` names the scripts' working directories. |
| `od`, `tail`, `wc`, `basename`, `dirname`, `diff` | The POSIX tools that the scripts of `checker/`, and `runner-fast/test.sh` through `checker/quote.sh`, use besides those above. `checker/quote.sh` writes an input as the string the checker reads: a file of only printable bytes and line feeds, as every file in the format is, a line at a time with `sed` and `awk`, which must take lines of any length, as those of macOS do (the library's proofs have a line of 300,527 bytes); any other file a byte at a time, with `od` writing its bytes as numbers and `awk` the string. |

## The checks

Wherever the specification states something about ACL2, a check confirms it against ACL2 itself. One command runs them all, from the root of the repository:

```
sh checks/run.sh
```

It writes its working files into `build/`, prints one line for each check, and ends with `all checks passed` or `some checks failed`. It was last run on 2026-11-21 with ACL2 8.7, and every line was `ok`.

| Check | What it confirms |
|---|---|
| `checks/version.lsp` | The `acl2` on the `PATH` is ACL2 8.7; otherwise `checks/run.sh` stops before any check, with status 3. |
| `checks/ground.lsp` | `spec/ground.txt` is, byte for byte, what ACL2 writes from its own world: its 32 primitive functions and the number of arguments of each; its 84 axioms, four of them as packages; the 122 symbols it refuses as variables; its definitions of the 37 functions that the ground theory defines, each with the ruler-extenders ACL2 stores; and the 23 clauses about `acl2-count` that its prover has built in, read from its constant `*initial-built-in-clauses*` as the check runs. ACL2 proves each of the 41 facts that the specification adds and each of those 23 clauses, and one that ACL2 did not prove would not be written. |
| `checks/facts.lsp` | `checks/expected/facts.txt` is, byte for byte, what ACL2 says. It holds: ACL2's list of 41 kinds of event; its value for 157 calls of the primitive functions, inside and outside their guards; which names, variables, axioms and packages it refuses; that the rule of the specification for a variable agrees with ACL2's on 3,613 objects; that the walk of the specification records the calls and tests of ACL2's termination machine for all 523 definitions that call themselves in the world ACL2 starts with; ACL2's conjectures for a definition admitted with another well-founded relation, and that the obligations of the specification follow from them; how ACL2 runs an attachment and that it uses none in a proof; how it treats a hidden package; the form of the axiom it stores for a function introduced by choice; the constraint it stores for an `encapsulate`; that it proves the conclusion of every step of the example proof; and counts over the world it starts with. |
| `checks/hidden.lsp`, `checks/outer.lsp` | ACL2 certifies the two small books `checks/hidden.lisp` and `checks/outer.lisp`, copied into `build/`, which give `checks/facts.lsp` a package that ACL2 keeps hidden. |
| `checks/edge.lsp` | `checks/expected/edge.txt` is, byte for byte, what ACL2 says on each entry of `EDGE-CASES.md`: its value for each example, under the setting of guard checking named, or that it gives none; whether it accepts or refuses each event and proof; what it stores for definitions, constraints, packages and the marks of skipped proofs, trust tags and redefinition; what its reader makes of 68 texts; and counts over the world it starts with. Each line other than a value or a reading is labelled with the number of its entry. |
| `checks/edge-hidden.lsp`, `checks/edge-false.lisp` | ACL2 certifies `checks/edge-hidden.lisp`, copied into `build/`, which gives `checks/edge.lsp` a symbol of the hidden package; `checks/edge-false.lisp`, copied into `build/`, is never certified. |
| `checks/reader.py` | A reader written from `spec/formats.md` reads every file of the repository that is in the format and writes each back unchanged. |
| The counts in `checks/run.sh` | The numbers that the documents give for the ground theory and for the kinds of event are those of the files, every fact of the ground theory is named in `spec/logic.md`, and that document lists the definitions of the ground theory in the order of the file. |

## The exporter

ACL2 writes its built-in library, and each book that `export/books.txt` names, in the formats of `spec/formats.md`: the statements, the program text for a runner, and, beside each book, the prover's aids. ACL2 reads each file back and confirms each line against its world, and `checks/reader.py` reads every file. One command does all of it, from the root of the repository:

```
sh export/run.sh
```

It writes its files into `build/export/`, and ends by writing `build/export/summary.txt`: the number of statements of each kind, the size in bytes of each file, and which books were exported and confirmed. A book is exported only if it has a valid certificate. `PLAN.md`, step 2, records the result of its last run.

Four commands read what it writes, and need `sh export/run.sh` to have been run first: `sh checks/agree.sh`, `sh checker/books.sh`, `sh runner/bench.sh` and `sh review/termination/run.sh`.

## The proofs of the exporter

The theorems of `PLAN.md`, step 4b, are proved in ACL2 about the core of the exporter and the printer: that the checker's reader reads back what the printer writes, that each line says what ACL2's world holds, that each name gets one statement or a note, that the statements stand in order, and that each line is of the format; and the guards of the core and of the printer are verified, so that, on any world that meets the guards of its entries, the core's compiled code gives the values of its definitions. `export/run.sh` exports with guard checking on, so that ACL2 checks those guards on each world it exports. One command certifies every book of the proofs and tests the hypotheses of their theorems on ACL2's worlds, from the root of the repository:

```
sh export/prove.sh
```

It runs the five scripts of `export/proofs/` one after the other, prints one line for each and ends with `all proofs passed` or `some proofs failed`. What each script printed is in `build/export/prove-NAME.out`, and the logs of ACL2 are in `build/export/acl2/`. It refuses a certificate that records a skipped proof, an added axiom or a trust tag. `PLAN.md`, step 4b, lists the theorems and records the result of its last run.

## The runner

The reference runner of `PLAN.md`, step 3, is in `runner/`; [`runner/README.md`](runner/README.md) says how to build and run it, what it conforms to and what it does at each stop. One command builds it and compares it with ACL2, from the root of the repository:

```
sh runner/test.sh
```

It prints one line for each set of cases and ends with `all runner tests passed` or `some runner tests failed`. `sh runner/bench.sh` times it against ACL2; `PLAN.md`, step 3, records both.

Run with `-j`, the runner starts with a prelude: `ash`, `binary-logxor`, `length`, `char` and `subseq`, which it computes itself, as ACL2 computes them by the code of the Lisp under it, and which ACL2's definitions compute only slowly: `ash` and `binary-logxor` not at all on integers of ordinary size, and the other three in time and memory in proportion to the length of a string. A define line for one of them is read and not used. `runner/README.md` says what the prelude is, why a define line for one of them can be left unused, and what it asks a reader to trust; `sh runner/prelude.sh` times each of the five with and without it. The checker calls `length` and `char`, and its commands give `-j`.

## The fast runner

The fast runner, in `runner-fast/`, is the reference runner made faster for development: it translates the definitions that a run reaches into C, compiles them with `cc`, keeps the objects in a cache under `build/runner-fast/`, and loads them. It takes the reference runner's arguments and must give its output and status; nothing trusts it, and the reference runner is the judge. [`runner-fast/README.md`](runner-fast/README.md) says how it works and what it was tested on. From the root of the repository,

```
make -f runner-fast/Makefile
```

writes `build/runner-fast/boymoo-run-fast`, and

```
sh runner-fast/test.sh
```

compares it with the reference runner, and needs `sh runner/test.sh` and `sh checker/build.sh` to have been run first. It prints one line for each set of cases and ends with `all fast runner tests passed` or `some fast runner tests failed`. The test itself needs neither ACL2 nor Python: `runner-fast/test/gen.awk` writes its calls, and where the definitions do not finish, so that the reference runner cannot be the judge, the values are ACL2's, kept in `runner-fast/test/expected/`; `sh runner-fast/test/record.sh`, which needs ACL2, records them again. `sh runner-fast/bench.sh`, which needs ACL2, times the two runners on the books of `runner/bench/`.

## The checker

The checker of `PLAN.md`, step 4, is in `checker/`. It is written in ACL2 Core: every function it defines calls only the 32 primitives, the 37 functions of the ground theory, the two functions of its library, `char` and `nth`, as ACL2 defines them, and its own, so that the runner can run it from its program text and it can be given its own statements. `checker/build.sh` writes its library, `build/checker/library.statements`, from the export of ACL2's library, which it writes first with `sh export/book.sh :library` if it is missing. ACL2 certifies its books, which proves that each of its functions terminates, and the exporter writes their program text. It reads each input as a string of bytes and does all the reading itself. From the root of the repository,

```
sh checker/check.sh LIBRARY STATEMENTS PROOFS [LIBRARY-PROOFS]
```

builds what it needs and prints the verdict of `spec/formats.md`, section 9, as its first line; the fourth file, the library's proofs, may be left out, and the fourth input is then empty. With `RUNNER=build/runner-fast/boymoo-run-fast` it runs on the fast runner. It gives the runner `-j`, and reads each input by position with `length` and `char`, which both runners then compute themselves, so that either judges a proof file as large as the library's proofs in one run. Its tests, run by

```
sh checker/test.sh
```

compare it, on the runner, with `spec/example` and with the expected verdict of every case of [`checker/cases/`](checker/cases), whose README lists the conditions of the specification that each case tests. A case is a directory that holds `library.txt`, `statements.txt`, `proofs.txt` and `library-proofs.txt`, the four inputs, a missing file being an empty input, and `verdict.txt`, the first line that a checker must write. The tests also confirm that it is written in ACL2 Core, and compute every verdict again inside ACL2. `sh checker/books.sh` runs it on the books of `export/books.txt`, with every obligation skipped.

ACL2 verifies the guards of the checker's functions, with the proofs of `checker/proofs/`:

```
sh checker/proofs/guards.sh --require-all
```

certifies the checker's books and the books of the proofs, refuses a certificate that records a skipped proof, an added axiom or a trust tag, checks that each function a guard calls is a primitive, a function of the ground theory or one of the checker's own, and ends with `all checker guard checks passed`; with `--require-all`, it fails unless the guard of every function is verified. The guard of `check-four`, which takes the ground theory and the four inputs, is that its five arguments are strings, so that ACL2 can run the checker's compiled code on any input; `check`, which takes three inputs and gives `check-four` an empty fourth, has the same guard on its four. [`checker/proofs/guards.md`](checker/proofs/guards.md) gives the guards, the invariants they rest on, and the functions whose bodies hold an `mbe`, and `PLAN.md`, step 5, what the guards show and do not.

The second checker, in `checker-js/`, is written from the specification alone, in JavaScript, and is run with `sh checker-js/check.sh LIBRARY STATEMENTS PROOFS [ENGINE]`, which gives an empty fourth input, or with `sh checker-js/check.sh LIBRARY STATEMENTS PROOFS LIBRARY-PROOFS ENGINE`. Its cases, in `checker-js/cases/`, are directories of the layout of `checker/cases/`. One command shows whether the two agree, as `PLAN.md`, step 4, asks:

```
sh checks/agree.sh [ENGINE]
```

Both must give `accepted` on `spec/example` and the expected verdict on every case of `checker/cases/` and of `checker-js/cases/`, each given its four inputs; and on each book of `export/books.txt`, with an empty fourth input, the two tools that write a skip for each obligation must write the same file, and the two checkers give the same verdict on it. It prints a line for each set and ends with `the two checkers agree` or `the two checkers do NOT agree`. `PLAN.md`, step 4, records the results.

## The review

The review of `PLAN.md`, step 5, tests the checker against ACL2, and has the checker check its own termination. Each of its three commands is run from the root of the repository.

```
sh review/steps/run.sh
```

has the checker, running inside ACL2, check `spec/example`, each case of `checker/cases/` and `checker-js/cases/` whose verdict is `accepted` or provisional and whose proofs or library's proofs hold a step, and the checker's own source, `build/checker/checker.statements` with the proofs `build/self/checker.proofs`, an empty library and empty library's proofs; requires the second checker to give the same verdict; writes, for each, an ACL2 book under `build/steps/` that states the conclusion of each step, of the library's proofs as of the proofs, as a theorem, with a `defchoose` for each `choose` statement and entry; and has ACL2 certify it. It prints a line for each proof, the totals for the cases, for the checker's source and for both, and ends with `all replayable proofs passed` or `some proofs failed`. It certifies its own copies of the checker's books, and needs no file that `export/run.sh` writes; when the checker's statements or proofs are missing or empty in `build/`, it writes them with `sh review/self/run.sh`, and otherwise takes them as they stand. Given a library, statements and proofs as three files, with the library's proofs as a fourth, which may be left out and is then empty, it does the same for that one input. [`review/steps/README.md`](review/steps/README.md) says how each statement and each rule becomes ACL2, and names the proofs that cannot be replayed, with their reasons.

```
sh review/termination/run.sh [BOOK ...]
```

gives the checker, for every definition with obligations in the ground theory, the library and each book of `export/books.txt`, or the books named, the measures that ACL2 stores, and compares the clauses the checker computes, clause for clause and in order, with ACL2's measure conjectures, exactly and then in a normal form made with ACL2's own functions. It prints a line for its book of cases, the ground theory, the library and each book, and ends with `all compared definitions agree` or `some definitions do not agree, or the comparison did not finish`. [`review/termination/README.md`](review/termination/README.md) gives the method, what is not compared and why, and the counts.

```
sh review/self/run.sh
```

writes, into `build/self/`, a proof of the obligations of termination of each definition of the checker's own statements, with no library, and has the checker on the runner and the second checker on Node check it; it prints the verdict and the time of each, and the number of definitions proved and of skips left. It also checks the proofs written for the checker's statements with each `mbe` replaced by its logical half. [`review/self/README.md`](review/self/README.md) says how the proofs are written, and gives their sizes.

`PLAN.md`, step 5, records the result of each.

## The prover

The prover of `PLAN.md`, step 6, is in `prover/`. It is written in ACL2 Core, like the checker: ACL2 certifies its books, which proves that each of its functions terminates, the exporter writes their program text, and the fast runner runs it. It finds proofs by any means; the checkers alone judge them. From the root of the repository, with ACL2 8.7, after `export/run.sh` and `make -f runner-fast/Makefile`, the books are certified and exported by

```
sh prover/build-all.sh
```

which runs `sh prover/build.sh`, then `sh prover/SET/build.sh` for each SET of `t2 t3 t4 b1 b2 h1 h2 h3 h4 l1`, four at a time, then `sh prover/driver/build.sh`, and ends with `All prover books are built.` Then

```
sh prover/driver/prove.sh [--sets A,B] LIBRARY STATEMENTS [AIDS]
```

prints the proof file for the statements, the sets named by `--sets` (all eleven if none are) being tried in turn.

```
sh prover/library.sh [-j JOBS] [-p PIECE] [-t SECONDS] [-s SETS] [-a | -f] OUT
```

proves the statements of the library and writes to `OUT` the library's proofs, the fourth input of a checker: the driver proves the library's obligations in pieces of consecutive lines, then alone each one a piece left, then each one still left with each set alone, in the order of `SETS`, by default `L1,H2,T1,H4,H3,B2,T3,B1,T2,T4,H1`; the proofs are joined in the order of the library, and an obligation that no run proved keeps its `skip` entry and is given. It keeps what each run gave under `build/prover/library/` and runs only what is not there; `-f` empties that folder first, as after a change to the prover. It ends with a line `N of 873 obligations of the library proved`. The header of the script says the rest.

```
sh prover/books.sh [-f | -l LIBRARY-PROOFS] BOOK ...
```

has the driver prove each book named, with the whole library as the library, leaves out of its proofs each helper entry that the library's proofs already state (`prover/tools/repeats.awk`), and has the checker in ACL2 Core, on the fast runner, and the second checker judge the book with the library's proofs as the fourth input; it ends with `All N books accepted by both checkers.` when every verdict is `accepted`. The library's proofs are `LIBRARY-PROOFS` with `-l`; without it the script first runs `sh prover/library.sh`, with `-f` if it is given, into `build/prover/library.proofs`, and stops if an obligation of the library is left unproved. So `sh prover/books.sh -f BOOK ...` is the test of `PLAN.md`, step 6, for a set of books, in one command.

After `sh review/termination/run.sh`, which writes the measures that ACL2 stores for the library, the tests are run by

```
sh prover/test-all.sh
```

which runs `sh prover/driver/test.sh` and then `sh prover/test.sh` and `sh prover/SET/test.sh` for the ten other sets, three at a time, and ends with `All prover tests passed.` or `Some prover tests failed.` For each input of a table (`prover/expected.tsv`, `prover/SET/expected.tsv`, `prover/driver/expected.tsv`), which is `spec/example`, one line of the library or an exported book, the driver, with the one set or with all eleven, writes a proof file, and the checker in ACL2 Core and the second checker judge it; the two verdicts must be the same, and the verdict and the number of obligations proved must be the table's. Each set's test ends with `All tests of prover/SET/expected.tsv passed.` and the driver's with `All driver tests passed.`; the driver's table has inputs that are lines of the library, whose aids are those measures. [`prover/CONVENTIONS.md`](prover/CONVENTIONS.md), "Building and testing", gives the rest. `PLAN.md`, step 6, records the results.

## Licence

Boymoo is published under the MIT No Attribution licence, MIT-0: see [`LICENSE`](LICENSE).
