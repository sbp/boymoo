# Plan

This is the order of the work on Boymoo, what each step gains, and how each is judged finished. [`README.md`](README.md) says what Boymoo is for. ACL2 Core is the language that [`spec/language.md`](spec/language.md) defines.

A step is finished when its test passes by one documented command, with the date and the result recorded where the claim is made.

## The steps

| | Step | State |
|---|---|---|
| 1 | The specification | Written; under review |
| 2 | The exporter, inside ACL2 | Written; its test passes |
| 3 | The reference runner, in C | Written; its test passes |
| 4 | The checker, in ACL2 Core, and a second checker beside it | Written; its test passes |
| 5 | Review: testing against ACL2, then the system on its own source | Not begun |
| 6 | The prover | Not begun |
| 7 | The compiler, in ACL2 Core | Not begun |
| 8 | Larger proof steps | Not begun |

### 1. The specification

**What it is.** The documents of `spec/`: the language, the logic and the interchange formats, with the ground theory as data, written so that two people who never speak could each write a checker and agree on every verdict.

**What it gains.** Everything after it is written from it. Each later step can be judged against a text instead of against a program.

**Finished when** `sh checks/run.sh` passes, so that every statement about ACL2 in the specification is confirmed by ACL2 8.7; and when a reviewer who attacks the seven steps of the argument in `spec/logic.md`, section 9, finds no step that fails.

### 2. The exporter, inside ACL2

**What it is.** A program run by ACL2 that writes, in the format of `spec/formats.md`:

- for a book, its statements, with the statements of the books it includes before them, each book once;
- for ACL2 itself, its built-in library: every function in logic mode and every theorem of the world ACL2 starts with, other than the ground theory. The definitions stand in an order in which each comes after the functions its body calls, and the functions with no definition are `constrain` statements (`spec/logic.md`, section 7);
- for both, the same definitions as program text for a runner, and with them the functions in program mode for which ACL2 has a definition in its own language. ACL2's world stores no body for the program-mode functions it starts with, so the exporter translates the events that defined them; and what some of them do is given only by Common Lisp code under ACL2, for which there is no program text (`spec/language.md`, section 7);
- beside each book, what has no logical content but helps a prover: the local events, the hints, and the measures and well-founded relations ACL2 used.

It takes each statement from ACL2's world, after ACL2 has processed the book: the stored body of a definition and the ruler-extenders stored with it, the stored formula of a theorem, the stored constraint of an `encapsulate`, the stored axiom of a `defchoose`, the imports ACL2 holds for a package and whether it keeps the package hidden, a `reserve` line for every other name the world has in use, and, in the program text, an `attach` line for every attachment in force.

**What it gains.** Every book that ACL2 can load becomes input at once, with no translator to write or trust beyond ACL2's own. It also gives the first measurements: the size of the statements of real books in a format where every symbol carries its package, which decides whether the format needs an abbreviation.

**Finished when**, for ACL2's built-in library and for a chosen set of books, one command writes the statements; the reader of `checks/reader.py` reads every file; ACL2, reading each file back, confirms that every statement is the event of its world with that name; and the number of statements of each kind is recorded.

**Where it stands.** The exporter is in `export/`, and `sh export/run.sh` runs it on the library and on the books that `export/books.txt` lists. Run on 2026-11-20 with ACL2 8.7, it took 280 seconds; every file it wrote was read by `checks/reader.py`; and ACL2, reading each back, confirmed every line of every file. Its counts and sizes are in `build/export/summary.txt`.

- **The library:** 4,151 statements: 3 `package`, 1,394 `define` (of 1,452 functions), 95 `constrain` (of 163 functions), 371 `theorem` and 2,288 `reserve`. Every function in logic mode of the world ACL2 starts with, other than the 36 of the ground theory, is introduced by exactly one statement, and so is each of its 519 theorems, 371 as `theorem` statements and 148 as formulas of a `constrain` statement. Its program text has 5,879 lines: the 36 definitions of the ground theory; 1,392 of the 1,394 definitions, all but those of `hard-error` and `throw-nonexec-error`, at which a runner stops as ACL2 does (`EDGE-CASES.md`, entry 2.2); 4,382 definitions of 4,701 functions in program mode, each `mbe` replaced by its executable half; and an `attach` line for each of the 69 attachments in force. The 111 other functions in program mode have no program text: the 106 that ACL2 lists as having raw code, and 5 whose definitions call functions that ACL2 allows only under a trust tag.
- **The books:** 460 chosen, all certified; all 460 exported, read back and confirmed. 458 are distributed with ACL2; `build/outer` is a book of `checks/run.sh`, and `build/choice` is `export/choice.lisp`, which holds two cases that no certified book of the distribution keeps. Of the 13,306 files `.lisp` under ACL2's directory of books in this installation, 958 have a certificate. A book is included only with a valid certificate (`:uncertified-okp nil`), so a book without one is not exported and is counted with the cause; no book chosen was refused. The chosen books include, for each kind of statement and each awkward case, a book that has it: `choose` (13 distinct lines, two of them strengthened), `axiom` (6), `hidden-package` (3, among them a package declared hidden and then openly), `defstobj` and `defabsstobj`, mutual recursion, relations other than `o<` (`l<` in `build/choice`, `e0-ord-<` in `ordinals/e0-ordinal`), attachments, program mode, fractions and complex rationals. Their statements, each book with those of the books it includes, number 113,576: 3,251 `package`, 3 `hidden-package`, 27,980 `define`, 729 `constrain`, 29 `choose`, 50,574 `theorem`, 6 `axiom` and 31,004 `reserve`; 15,411 lines are distinct. Beside them, the prover's aids hold 3,039 local events, 7,001 hints, 2 sets of instructions and 1,191 measures, 148 declared and 1,043 chosen by ACL2.
- **Sizes:** the library's statements are 3,077,290 bytes and its program text 48,361,580; the books' statements 230,930,855 bytes in all, their program text 88,380,274 and their aids 11,730,510. Of the library's statements, package names with their `::` are 45% of the bytes; of the books', the package lines are 80%, since each book carries the packages of the books it includes, and package names are 51% of the rest. Nearly all of those names are `ACL2::` and `COMMON-LISP::`. `gzip -9` reduces the library's statements to 9% of their size, and the books' to 18%.
- **What the formats could not say as ACL2 does.** ACL2 holds the definition of a function defined inside an `encapsulate` under the function's own name, and some formulas of a constraint, the corollaries of rule classes, under none; a `constrain` statement, which may not introduce one name twice, names these formulas `F definition` and `C constraint N` (2 in the library, 18 in the books). Where ACL2 records no constraint, as for 14 `encapsulate` events of the library, the formulas are the theorems ACL2 holds about the functions. The statement `constrain` of an `encapsulate` stands after the statements of the events inside it that are not part of its constraint, which cannot mention its functions, since its formulas may mention theirs. The notes of each book mark what ACL2 records of trust tags (10 books), of certificates that record axioms (1) or skipped proofs (none) and of redefinition (none); the exporter refuses none of these.

### 3. The reference runner, in C

**What it is.** A small program in C that reads program text in the format and computes the value of a term, by the definition of value in `spec/language.md`, section 4: the seven kinds of data with integers of any size, the 32 primitive functions, and calls of defined functions. It runs an attachment in place of a function that has one, and stops at a call of a function that has neither a definition nor an attachment, as ACL2 does.

**What it gains.** The durable base: a checker written in ACL2 Core can be run with nothing but a C compiler, and later with no C compiler at all (step 7). It is not trusted for any proof; it is trusted to compute, and it is small enough to read.

**Finished when** it gives ACL2's value on the calls of `checks/expected/facts.txt` that ACL2 Core computes and on a set of programs taken from ACL2's library, compared with ACL2 by one command; and when its size in lines is recorded.

**Where it stands.** The runner is in `runner/`: 2,309 lines of C that are neither blank nor wholly comment (`sh runner/size.sh`, 2026-11-20), in ISO C99 with nothing beyond the library of C, built by a `Makefile` for the `make` of POSIX. `runner/README.md` says how to build, run and test it, what it conforms to, and what it does at each stop. It needs the packages as well as the program text, and `spec/formats.md`, section 5, now says where it takes them from, and which of two `define` lines for one function is in force.

- **The test.** `sh runner/test.sh`, run on 2026-11-20 with ACL2 8.7, printed `all runner tests passed`, both for the build of the `Makefile` and for a build with the address and undefined-behaviour sanitizers. The runner gave ACL2's value on the 153 calls of `checks/expected/facts.txt` that ACL2 computes and stopped at the 4 that it refuses; did the same on the 75 and the 1 of `checks/expected/edge.txt`; on the 18 calls of `runner/test/book.lisp`, a book of stops (11 values, 7 stops); on 2,150 calls of 86 functions of ACL2's library, run from its program text; and on 4,000 calls of the arithmetic primitives on large integers, fractions and complex rationals. It ran a recursion a million calls deep, read and wrote a datum nested a million levels deep and numbers of a million digits, stopped cleanly where memory ran out and on text that is not in the format, and read and compiled every definition of the library and of the 460 books of step 2.
- **Loading.** The library's program text is 48 MB. Indexing it and compiling each definition at its first call takes 0.08 seconds and a peak of 66 MB, most of it the text; compiling all 6,187 definitions at once takes 0.35 seconds and 224 MB. The runner does the first (`runner/README.md`).
- **Against ACL2 8.7 on SBCL.** `sh runner/bench.sh`, run on 2026-11-20, certified the eleven books of `runner/bench/`, whose guards are verified, and timed the same call in ACL2 and in the runner. Times are seconds of elapsed time, medians of three runs. ACL2's time for the call is that of twenty calls divided by twenty; its process starts ACL2, includes the book and makes the call. The runner's process reads the program text of the library and of the book and makes the call; the time to read the text alone is shown apart. The peak is the runner's memory. Every value was ACL2's.

  | Book | ACL2, the call | ACL2, the process | Runner, the process | Runner, reading only | Runner's peak (MB) |
  |---|---:|---:|---:|---:|---:|
  | `fib`: recursion on integers | 0.0130 | 0.14 | 0.27 | 0.08 | 67 |
  | `loop`: a loop in the last position | 0.1415 | 0.27 | 0.82 | 0.08 | 67 |
  | `lists`: building and walking lists | 0.0415 | 0.17 | 0.56 | 0.08 | 69 |
  | `sort`: a merge sort | 0.0475 | 0.19 | 0.60 | 0.08 | 72 |
  | `alist`: association lists | 0.0125 | 0.15 | 0.34 | 0.08 | 67 |
  | `fact`: the factorial of 6,000 | 0.0020 | 0.24 | 0.11 | 0.08 | 68 |
  | `power`: 7 to the power 40,000 | 0.0270 | 0.47 | 0.46 | 0.08 | 70 |
  | `fractions`: a harmonic sum | 0.0020 | 0.13 | 0.08 | 0.08 | 68 |
  | `chars`: characters and strings | 0.0685 | 0.21 | 0.49 | 0.08 | 93 |
  | `symbols`: making and sorting symbols | 0.0305 | 0.17 | 0.23 | 0.08 | 68 |
  | `library`: functions of ACL2's library | 0.0830 | 0.22 | 1.01 | 0.08 | 68 |

  The runner's time for the call, its process less its reading, is 5 to 21 times ACL2's compiled code, and is below the resolution of the measure for `fractions`. Its whole process takes less time than ACL2's for `fact` and `fractions`, about as much for `power`, and up to 4.6 times as much for the others.

### 4. The checker, and a second checker

**What it is.** The checker of `spec/logic.md`, written in ACL2 Core, so that the runner of step 3 runs it and it can later check itself. Beside it, a second checker written from the specification alone, in another language and without sight of the first.

**What it gains.** Every book gets at least a provisional verdict: with the library given and every proof skipped, the verdict says how much remains to be proved, and it already confirms that the statements are well formed, that every name is new and every symbol exists. Two checkers that agree are the test of the specification's first claim.

**Finished when** both give `accepted` on `spec/example`; both give the same first line on every input of a set of tests that has at least one rejection for each condition of the specification; and both give the same provisional verdict on every book of step 2.

**What keeps the test worth something.** A change to either checker is made from the specification, never from the other checker's code: neither checker's source is read to write or change the other. Where the two disagree, the specification is made to say what it means, each checker is changed from that text, and both are run again. Each keeps its own cases, and each is run on the other's.

**Where it stands: the checker in ACL2 Core.** It is in `checker/`: six ACL2 books in the package of `checker/package.lsp`, 1,671 lines that are neither blank nor wholly comment (`sh checker/size.sh`, 2026-11-20). ACL2 8.7 certifies them in logic mode, which proves that each of their 190 functions terminates; their guards are not yet verified, which is step 5. The exporter writes them as 182 `define` lines, one `package` line and 27 `reserve` lines. The checker takes the bytes of `spec/ground.txt` and of the three inputs as four strings and does all the reading itself, so that a line that is not in the format is a rejection and never a stop of the runner; `sh checker/check.sh LIBRARY STATEMENTS PROOFS` writes the strings with `od` and `awk`, has the runner compute the verdict from the checker's program text, and prints it. The runner is unchanged. As in ACL2, a call in the executable half of an `mbe` does not make a definition recursive (`spec/logic.md`, section 6), so the library has 502 given definitions, ACL2's own `string-append` not among them.

- **The test.** `sh checker/test.sh`, run on 2026-11-20, printed `all checker tests passed`. On the runner, `spec/example` gave `accepted`; each of the 309 cases of `checker/cases/` gave its verdict, among them at least one rejection for each of the 74 conditions that `checker/cases/README.md` lists with the section that states it; every function called in the checker's `define` lines is a primitive, a function of the ground theory or one of its own (`checker/closed.py`); and the checker's own statements, with an empty library and a skip for each of their 87 obligations, gave `provisional skipped 87 assumed 0 given-definitions 0 given-facts 0`. ACL2, computing the same functions on the same bytes, gave the same verdict on all 311 inputs.
- **Time.** Measured on 2026-11-20 with `-v`: on the runner, admitting the library, 4,151 statements and 3 MB, takes 1.45 seconds of processor time and a peak of 159 MB; with the largest book, `std/strings/pretty`, 3,918 statements and 2.3 MB, and its 2,500 skips, the run takes 3.07 seconds and a peak of 180 MB. Inside ACL2 the same take about 0.7 and 1.5 seconds (`sh checker/acl2-check.sh`, six runs less one, divided by five). Writing the bytes as strings with `od` and `awk` takes about 1.4 seconds for the library.
- **The books.** `sh checker/books.sh`, run on 2026-11-20, ran the checker on the runner on all 460 books of step 2, with `build/export/library.statements` as the library and a skip for each obligation, which `checker/skips.py` writes into `build/checker/skips/`; it took 995 seconds, of which the runner's part is about two seconds a book and the rest the shell and the skips, and wrote the verdicts to `build/checker/books.txt`. Every verdict is provisional, with the 502 given definitions and 371 given facts of the library; the books skip 61,068 obligations in all, from 0 in 36 books to 2,500 in `std/strings/pretty`, and one book, `misc/dft-ex`, assumes 6 axioms. ACL2 gave the same verdict on every book (`sh checker/acl2-check.sh < build/checker/books-list.txt`, 418 seconds).

**Where it stands: the second checker.** It is in `checker-js/`: `checker-js/check.js`, 1,515 lines of ECMAScript 5.1 that are neither blank nor comment (the command in `checker-js/README.md`, run on 2026-11-20), written from the specification alone, with adapters for Node, JavaScriptCore, Duktape, QuickJS and a browser, and 327 cases of its own in `checker-js/cases/`, in the layout of `checker/cases/`. `sh checker-js/check.sh LIBRARY STATEMENTS PROOFS [ENGINE]` runs it; `checker-js/README.md` gives its other commands.

- **The test.** `sh checker-js/test.sh node`, run on 2026-11-20 with Node 22.14.0, printed `all checker tests passed`: `spec/example` gave `accepted` and each of its 327 cases gave its verdict.
- **Time.** `node checker-js/books.js node`, run on 2026-11-20, admitted the library in 0.12 seconds and checked all 460 books in 41 seconds, with the verdicts of the first checker. The same command with `jsc` gave 0.12 and 68 seconds, and with `duk`, Duktape 2.7.0, 2.1 seconds and a peak of 99 MB for the library, on twenty books (2026-11-20).

**Where it stands: the two together.** `sh checks/agree.sh`, run on 2026-11-20 with Node 22.14.0, printed `the two checkers agree`, in 1,155 seconds: both gave `accepted` on `spec/example`; both gave the expected verdict on each of the 309 cases of `checker/cases/` and the 327 of `checker-js/cases/`, which together hold at least one rejection for each condition of the specification; on each of the 460 books of step 2, the two tools that write a skip for each obligation, `checker/skips.py` and `checker-js/skips.js`, wrote the same file, and the two checkers gave the same verdict. The readings on which a verdict could depend and which the text might be taken to leave open, among them which line fails when the proofs end, are stated in it: `spec/formats.md`, sections 6 to 8; `spec/logic.md`, sections 3, 6 and 9; `spec/language.md`, sections 5 and 6. One difference from ACL2 waits on a decision (see "Undecided": a package of the ground theory declared again).

### 5. Review

**What it is.** First, testing against ACL2: for every proof that the checkers accept, a book that states the conclusion of each step as a theorem, which ACL2 must certify; and for every definition, a comparison of the obligations of termination with ACL2's own measure conjectures. Then the system on its own source: the proofs of termination of the checker's own functions, checked by the checker, and of the guards of its functions. Guards are no part of the logic; here they are theorems which show that the checker's code never calls a primitive outside the arguments it is meant for, so that it may be compiled without checks.

**What it gains.** Confidence from two directions: ACL2 agrees with every step the checker took, and the checker's own source is among the things it has checked.

**Finished when** ACL2 certifies the book of steps for every accepted proof, and the checker gives `accepted`, with an empty library, on its own source.

### 6. The prover

**What it is.** A program that finds proofs in the eight rules. It works upward from the built-in library: first the termination of ACL2's own definitions and the theorems ACL2 holds about them, then the books. It may use anything to find a proof, the hints and local events of step 2 among them, since the checker judges the result. For termination it gives each definition a measure built from the functions in use at that definition. ACL2's own measure is a starting point and not always usable as it stands: it may call a function that comes later, be stated with another well-founded relation, or not be stored at all (`spec/logic.md`, sections 6 and 7).

**What it gains.** What was given or skipped becomes proved. Each count of a provisional verdict falls, and a book reaches `accepted` when its counts and those of everything it rests on reach 0.

**Finished**, for a set of books, when the verdict on each is `accepted`: nothing skipped, nothing assumed and nothing given, the library's own statements being proved too. How the library's proofs reach a checker is not settled (see "Undecided").

### 7. The compiler

**What it is.** A compiler from ACL2 Core to machine code, written in ACL2 Core. The reference runner runs it once to compile itself.

**What it gains.** Speed, and a stack with no C compiler under it: the checker, compiled by a compiler that the checker's own logic can reason about.

**Finished when** the compiled compiler, compiling its own source, gives its own bytes again; and the compiled checker gives the verdict of the runner's checker on every input of step 4, in a recorded fraction of the time.

### 8. Larger proof steps

**What it is.** Rules that do in one step what takes many in the kernel: the opening of a definition, rewriting with a lemma, evaluation of a defined function on constants with a budget of steps, the use of a theorem about constrained functions at other functions that meet the constraints, and arithmetic. Each is a function from its premises to a conclusion, admitted only with a proof, at the level below, that its conclusion always follows.

**What it gains.** Shorter proofs and faster checking, with the trusted rules still the eight.

**Finished**, for each rule, when its proof of soundness is accepted by the checker and the size of the proofs of step 6 with and without it is recorded.

## Undecided

These matters are not settled, and the specification says so where they arise.

- **The copyright line of `LICENSE`,** which reads "Copyright 2026 the Boymoo authors".
- **A notice for what is ACL2's.** `spec/ground.txt`, `checks/expected/facts.txt` and `checks/expected/edge.txt` hold ACL2's own axioms and definitions, as ACL2 writes them. ACL2 is distributed under its own licence, and whether these files need its notice is not settled.
- **Recursion inside the quoted lambda of a `loop$`,** which ACL2 measures and ACL2 Core does not yet (`EDGE-CASES.md`, entry 6.14).
- **A `choose` entry in the proofs.** `defun-sk` makes a `constrain` statement whose formulas, in general, only a choice function meets, and a proof may define functions but not introduce one by choice, so such a statement can only be skipped (`EDGE-CASES.md`, entry 6.9). A `choose` entry, admitted as a `choose` statement is, would let a proof hold the local `defchoose` that ACL2 used. It would add a word to `spec/formats.md`.
- **The values of the character functions with unknown constraints.** ACL2 proves by running the Common Lisp under it what `char-upcase`, `char-downcase`, `upper-case-p`, `lower-case-p` and `alpha-char-p` give on the 160 characters that are not standard, and decides by the same code whether a package name has a lower-case character (`EDGE-CASES.md`, entries 1.4 and 7.2). The library could hold these 800 values as theorems; they depend on the host. The double-floats of entry 1.5 have no such finite table.
- **What program text says beyond definitions.** A runner differs from ACL2 where ACL2 runs the executable half of an `mbe` because a function's guards are verified, and where ACL2 refuses a constant in place of a single-threaded object (`EDGE-CASES.md`, entries 2.5, 2.7 and 3.4). Program text that marked guard-verified definitions and single-threaded arguments would let a runner stop where ACL2 does.
- **Names that ACL2 refuses for reasons outside the logic.** ACL2 refuses a function named by a symbol that the Lisp under it defines, a package named as one of that Lisp's packages, and any event that calls a function it holds untouchable; ACL2 Core refuses none of these (`EDGE-CASES.md`, entries 6.1 and 7.2). The library could reserve the names of one host and mark the untouchable functions.
- **A package of the ground theory declared again.** ACL2 accepts `(defpkg "KEYWORD" nil)` and `(defpkg "COMMON-LISP" nil)` as redundant. ACL2 Core refuses the `package` statement `(package "KEYWORD" COMMON-LISP::NIL)`, although it is, byte for byte, a line of the ground theory, because the ground theory is no input and a package may not be declared twice (`spec/logic.md`, section 6; `EDGE-CASES.md`, entry 7.1). The case `checker/cases/reject-repeat-ground-package` shows it. No statement that ACL2 writes is affected.
- **A world that a trust tag, redefinition, skipped proofs or a book with no certificate has changed.** ACL2 records each of these in its world (`EDGE-CASES.md`, entries 8.2 to 8.5). Every statement still needs its proof, but a world changed under a trust tag may hold what the book's text does not say. Whether the exporter refuses such a world, or marks what it writes from it, is not settled.
- **How the library's own definitions are proved.** A book may not define a function whose name is a symbol of `COMMON-LISP`, as in ACL2, and ACL2's library defines 94 of them. So the library cannot simply be moved to the second input of a checker to be proved. One way is a fourth input that holds proofs for the library.
- **Whether a symbol may be abbreviated.** Every symbol is written with its package (`spec/formats.md`, section 4). Step 2 measured what that costs: about half the bytes of every statement other than a package line, nearly all of it `ACL2::` and `COMMON-LISP::`; while the package lines are 80% of the bytes of the books' statements, and `gzip -9` leaves 9% to 18% of the size, with the format unchanged.
- **How a rejection names what failed.** The verdict gives the input and the number of the line (`spec/formats.md`, section 9), not a symbol.
- **Code of the runner's own for functions of the library.** ACL2 computes `floor`, `mod`, `nonnegative-integer-quotient` and some 280 other functions of its library with code of the Lisp under it (`EDGE-CASES.md`, entry 3.3). The runner runs their definitions, by which `(nonnegative-integer-quotient i j)` subtracts `j` from `i` once for each unit of the quotient, so that `floor` of a large number by a small one does not finish (`runner/README.md`). The runner could hold code of its own for a few such functions; it would then be trusted to compute what their definitions compute.
