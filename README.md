# Boymoo

Boymoo is an independent checker for the [ACL2](https://www.cs.utexas.edu/~moore/acl2/) theorem prover. It has two goals.

1. **A checker small enough to audit.** It accepts a theorem only with a proof written out in primitive steps, and it does not rest on ACL2's own word that the theorem is proved.
2. **Durability.** A proof can be checked with a small stack of software that contains neither ACL2 nor Common Lisp.

Its watchwords are that it be auditable, minimal and efficient, and that it reuse as much existing ACL2 work as it can: every book that ACL2 can load is to become input for it.

## How it works

ACL2 is the front end. It reads a book, expands every macro, and writes what the book states as plain **statements**: definitions, theorems, axioms, functions introduced by constraint or by choice, and packages. What remains of ACL2's language after that expansion is small: seven kinds of data, 32 primitive functions, terms, and eight kinds of statement. This repository calls it **ACL2 Core**. ACL2's documentation names the parts, translated terms and primitive event macros; the name for the whole is this project's.

ACL2 is the definition of ACL2. Wherever ACL2 decides something, by its axioms, by its evaluator or by the tests it makes before it admits an event, ACL2 Core decides the same, and a check confirms it against ACL2.

A **checker** reads three things: a library of statements that are taken as given, the statements of a book, and a file of proofs. It answers with one line:

- `accepted`: every theorem follows, by eight rules of inference, from ACL2's axioms and the book's own statements;
- `provisional`, with four counts: the same, except for the proofs that were skipped, the axioms that were assumed, and the definitions and facts of the library that were given;
- `rejected`, with the place of the first line that fails.

ACL2 says what a book states and is used to cross-check. It takes no part in finding or checking a proof.

## What is in the repository

The repository holds the specification, the checks that compare it with ACL2, the exporter, by which ACL2 writes its library and its books in the formats, the reference runner, which computes the value of a term from program text, a checker written in ACL2 Core, which the runner runs, and a second checker, written apart from it in JavaScript. [`PLAN.md`](PLAN.md) gives the order of the work.

| Path | What it is |
|---|---|
| [`spec/language.md`](spec/language.md) | The language: data, the 32 primitive functions and their value on every input, running and attachments, terms, names, the eight kinds of statement, and what each kind of ACL2 event becomes. |
| [`spec/logic.md`](spec/logic.md) | The logic: the axioms, the eight rules with the argument that each is sound, how each statement is admitted and what must be proved for it, what a verdict means, with the argument for it, and the facts beyond ACL2's axioms that ACL2 itself reasons with. |
| [`EDGE-CASES.md`](EDGE-CASES.md) | Every place found where what ACL2 does goes beyond, falls short of or differs from what its axioms say, with an example of each that the checks run, what ACL2 Core does there, and why where it does not follow ACL2. |
| [`spec/formats.md`](spec/formats.md) | The interchange formats: the text of data, statements and proofs, the order of checking, the budgets, and the three verdict lines. |
| [`spec/ground.txt`](spec/ground.txt) | The ground theory that every checker holds: ACL2's packages, primitives and axioms, and the definitions they mention, as data. ACL2 writes it. |
| [`spec/example/`](spec/example) | One theorem and its proof in seven steps, in the formats. |
| [`checks/`](checks) | The checks: scripts and four small books for ACL2, a reader for the formats, the expected results, and `run.sh`, which runs them all. |
| [`export/`](export) | The exporter: a program run by ACL2 that writes its built-in library and its books as statements, program text and the prover's aids (`export.lsp`), a check by which ACL2 reads each file back (`readback.lsp`), the books chosen (`books.txt`) with a small book of two cases of its own (`choice.lisp`), and `run.sh`, which runs it all. |
| [`runner/`](runner) | The reference runner: a program in ISO C99 that reads program text and computes the value of a term (`runner/README.md`), its `Makefile`, its tests against ACL2 (`test.sh`, with the files of `runner/test/`), and its benchmarks against ACL2 (`bench.sh`, with the books of `runner/bench/`). |
| [`checker/`](checker) | The checker of `spec/logic.md`, in ACL2 Core: six ACL2 books in the package of `package.lsp`, which read the three inputs as strings and give the verdict (`base.lisp`, `read.lisp`, `terms.lisp`, `rules.lisp`, `admit.lisp`, `check.lisp`); `build.sh`, which has ACL2 certify them and the exporter export them; `check.sh`, which runs the checker on the runner, with the shell functions of `quote.sh`; `acl2-check.sh`, with `acl2-run.lsp`, which runs the same functions inside ACL2; its tests, `test.sh`, with the cases of `checker/cases/` and the tools `closed.py` and `skips.py`; `books.sh`, which runs it on the books of `export/books.txt`; and `size.sh`. |
| [`checker-js/`](checker-js) | The second checker of `PLAN.md`, step 4, written from the specification alone in ECMAScript 5.1 (`check.js`), with adapters for several JavaScript engines and a browser, its cases (`checker-js/cases/`), its tests and its tools; [`checker-js/README.md`](checker-js/README.md) gives its commands. |
| [`LICENSE`](LICENSE) | The licence. |
| [`PLAN.md`](PLAN.md) | The steps of the work, what each gains, and how each is judged finished. |
| [`AGENTS.md`](AGENTS.md) | The rules that bind every change to this repository. |

A reader new to the project should read `spec/language.md`, then sections 1, 5, 6, 9 and 10 of `spec/logic.md`, then `spec/formats.md`, and then `EDGE-CASES.md` for where ACL2 and its axioms part.

## Tools

Every tool is found by its name on the `PATH`.

| Tool | Used for |
|---|---|
| `acl2` | ACL2 version 8.7, with the books that are distributed with it, of which `projects/apply/top` must be certified. The checks ask ACL2 what it holds, have it prove the facts that the specification adds to its axioms, and have it certify three small books of their own in `build/`. The checks and the exporter run under this version only: they read properties of ACL2's world, which can change from one version to the next without notice, so that another version could give a wrong answer and report no error. ACL2 loads [`checks/version.lsp`](checks/version.lsp), the one place that names the version, at the start of the first run of `checks/run.sh` and of every run of `export/book.sh`; under any other version it ends at once, and the script prints the version it found and stops with status 3. |
| `python3` | Python 3.5 or later, for `checks/reader.py`, the reader of the formats, `export/measure.py`, which counts and measures what the exporter writes, the files of `runner/test/` that write the runner's test cases, and the test tools `checker/closed.py` and `checker/skips.py`. |
| `make`, `c99` | The `make` and the C compiler of POSIX, to build the runner (`runner/Makefile`); the compiler may be named otherwise with `CC`. Nothing else is needed to build or run the runner. |
| `sh`, `cmp`, `cp`, `grep`, `sed`, `tr`, `paste`, `rm`, `mkdir`, `date`, `cat` | The usual POSIX tools, for `checks/run.sh` and `export/run.sh`. |
| `timeout`, `xargs` | For `export/run.sh`: `timeout` (of GNU coreutils) stops a run of ACL2 on one book after 30 minutes, and `xargs`, with its option `-P`, runs two at a time. |
| `awk`, `env`, `time`, `sort`, `paste`, `head`, `cut`, `mv` | The POSIX tools that `runner/test.sh` and `runner/bench.sh` use besides those above. |
| `node`, or `duk`, `qjs`, `jsc` | A JavaScript engine, for the second checker (`checker-js/README.md`); `checks/agree.sh` uses `node` unless another is named, and `node` for the tool that writes the second checker's skips. |
| `od`, `basename`, `dirname`, `diff` | The POSIX tools that the scripts of `checker/` use besides those above: `od` writes the bytes of an input as numbers, from which `awk` writes the string the checker reads. |

## The checks

Wherever the specification states something about ACL2, a check confirms it against ACL2 itself. One command runs them all, from the root of the repository:

```
sh checks/run.sh
```

It writes its working files into `build/`, prints one line for each check, and ends with `all checks passed` or `some checks failed`. It was last run on 2026-11-20 with ACL2 8.7, and every line was `ok`.

| Check | What it confirms |
|---|---|
| `checks/version.lsp` | The `acl2` on the `PATH` is ACL2 8.7; otherwise `checks/run.sh` stops before any check, with status 3. |
| `checks/ground.lsp` | `spec/ground.txt` is, byte for byte, what ACL2 writes from its own world: its 32 primitive functions and the number of arguments of each; its 84 axioms, four of them as packages; the 122 symbols it refuses as variables; and its definitions of the 36 functions that the ground theory defines, each with the ruler-extenders ACL2 stores. ACL2 proves each of the 41 facts that the specification adds, and a fact that ACL2 did not prove would not be written. |
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

## The runner

The reference runner of `PLAN.md`, step 3, is in `runner/`; [`runner/README.md`](runner/README.md) says how to build and run it, what it conforms to and what it does at each stop. One command builds it and compares it with ACL2, from the root of the repository:

```
sh runner/test.sh
```

It prints one line for each set of cases and ends with `all runner tests passed` or `some runner tests failed`. `sh runner/bench.sh` times it against ACL2; `PLAN.md`, step 3, records both.

## The checker

The checker of `PLAN.md`, step 4, is in `checker/`. It is written in ACL2 Core: every function it defines calls only the 32 primitives, the 36 functions of the ground theory and its own, so that the runner can run it from its program text and it can later be given its own statements. ACL2 certifies its books, which proves that each of its functions terminates, and the exporter writes their program text. It reads each input as a string of bytes and does all the reading itself. From the root of the repository,

```
sh checker/check.sh LIBRARY STATEMENTS PROOFS
```

builds what it needs and prints the verdict of `spec/formats.md`, section 9, as its first line. Its tests, run by

```
sh checker/test.sh
```

compare it, on the runner, with `spec/example` and with the expected verdict of every case of [`checker/cases/`](checker/cases), whose README lists the conditions of the specification that each case tests; confirm that it is written in ACL2 Core; and compute every verdict again inside ACL2. `sh checker/books.sh` runs it on the books of `export/books.txt`, with every obligation skipped.

The second checker, in `checker-js/`, is written from the specification alone, in JavaScript, and is run with `sh checker-js/check.sh LIBRARY STATEMENTS PROOFS [ENGINE]`. One command shows whether the two agree, as `PLAN.md`, step 4, asks:

```
sh checks/agree.sh [ENGINE]
```

Both must give `accepted` on `spec/example` and the expected verdict on every case of `checker/cases/` and of `checker-js/cases/`; and on each book of `export/books.txt`, the two tools that write a skip for each obligation must write the same file, and the two checkers give the same verdict on it. It prints a line for each set and ends with `the two checkers agree` or `the two checkers do NOT agree`. `PLAN.md`, step 4, records the results.

## Licence

Boymoo is published under the MIT No Attribution licence, MIT-0: see [`LICENSE`](LICENSE).
