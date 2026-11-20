# The reference runner

The reference runner of `PLAN.md`, step 3: a small program in C that reads program text in the format of `spec/formats.md` and computes the value of a term by `spec/language.md`, section 4. It holds the seven kinds of data, with integers of any size, computes the 32 primitive functions by the table of `spec/language.md`, section 3, runs defined functions and attachments, and stops where ACL2 Core gives no value. At each edge it does what `EDGE-CASES.md` says a runner does.

Paths below are given from the root of the repository, from which every command is run.

## Building

```
make -f runner/Makefile
```

writes `build/runner/boymoo-run`. The `Makefile` is for the `make` of POSIX.1-2001 and calls the compiler by its POSIX name, `c99`, with `-O 1`; `CC`, `CFLAGS`, `LDFLAGS` and `OUT`, the directory written, may be given on the command line. Nothing but a C compiler and its library is needed to build or run the runner.

## Running

```
build/runner/boymoo-run [-l] [-v] [-m megabytes] [-p packages] ... program ...
```

The runner reads its files in the order given. A file named by `-p` is the ground theory or a file of statements, from which it takes the `package` and `hidden-package` lines and skips every other line; every other file is program text, of `define` and `attach` lines. Then it reads standard input, a term on each line in the text of a datum, and writes the value of each on a line of standard output in the same text. The output can be compared, byte for byte, with what ACL2 prints through `checks/canon.lsp`. To run a term on ACL2's library and a book, whose exported files `export/run.sh` writes:

```
echo '(ACL2::BINARY-APPEND (COMMON-LISP::QUOTE (1 2)) (COMMON-LISP::QUOTE (3)))' |
  build/runner/boymoo-run -p spec/ground.txt -p build/export/library.statements \
    -p BOOK.statements build/export/library.program BOOK.program
```

prints `(1 2 3)`. The packages are needed because `intern-in-package-of-symbol`, `pkg-imports`, `pkg-witness` and `symbol-package-name` depend on them (`spec/formats.md`, section 5); `ACL2-PC`, for one, is declared only in the library's statements.

| Option | Meaning |
|---|---|
| `-l` | Read and compile every definition when the files are read, not when each is first called. |
| `-v` | At the end, write to standard error the processor time taken to read the files and to compute, the number of definitions compiled and of collections, and the peak of memory held. |
| `-m N` | Hold at most `N` megabytes (default 4096): the heap, the stacks, the program text and every table. |

The exit status is 0 when every term has a value, and otherwise that of the first stop, below.

## The stops

Every run ends in values or in a stop: a message on standard error, which names the file and line or the line of standard input, and one of three statuses. The values written before a stop stand.

| Status | Stop | Where the specification says so |
|---|---|---|
| 1 | A call of a function that has no definition and no attachment: a function of a `constrain` or a `choose` statement with no `attach` line, `hard-error` and `throw-nonexec-error`, and so `illegal`, `er hard` and every function that is not executable, and every function for which the program text holds no definition. | `spec/language.md`, sections 4 and 7; `EDGE-CASES.md`, entries 2.1 to 2.3, 1.4, 3.2 and 10.3 |
| 1 | `pkg-imports` or `pkg-witness` of a string that names no package or names a hidden one. | `spec/language.md`, section 4; entry 2.8 |
| 1 | `symbol-package-name` of a symbol of a hidden package. | entry 2.9 |
| 2 | Text that is not in the format: a byte outside 32 to 126, a line that is not the one text of its data, a line whose word may not stand in its file, a symbol of a package that is not declared or that does not exist (`spec/language.md`, section 2), a package declared again with other imports. A term that is not a term: a variable that is not bound, a call with the wrong number of arguments, a lambda whose formals are not distinct variables. A define line that defines a primitive, or one function twice; attachments that form a cycle; a term nested more than 10,000 levels deep. A file that cannot be read; a wrong command line. | `spec/formats.md`, sections 1, 2 and 5; `spec/language.md`, sections 2 and 5 |
| 3 | Memory exhausted: the limit of `-m` is reached, or the system refuses memory. | entry 2.6 |

## How it works

The sources are `run.h`, the declarations; `heap.c`, memory; `num.c`, numbers; `data.c`, symbols, packages and the text of data; `eval.c`, definitions, the compiler and the machine; and `sys.c`, the only file that touches the system. The size, in lines that are neither blank nor wholly comment, is printed by `sh runner/size.sh`.

**Data.** A datum is a word of 32 bits. Its low bits tell an immediate integer from -2<sup>29</sup> to 2<sup>29</sup> - 1, a character, a symbol (an index into a table of symbols that is never collected), a cons (an index into the space of conses) or a box (an offset into the space of boxes, which holds larger integers, fractions, complex rationals and strings). Every datum has one representation, so data that are not conses or boxes are equal exactly when their words are. A larger integer holds its magnitude in base 10<sup>9</sup>, so that reading and writing a number takes time in proportion to its length; multiplication and division are the schoolbook's and Knuth's, greatest common divisors are Euclid's, and fractions are added and multiplied by Knuth's method, which divides out only what can be common.

**Memory.** The two spaces are collected by copying, by Cheney's method, which needs no stack however deep the data. The roots are the machine's value stack, on which every datum in use is kept, and the table of the program's constants. After a collection each space is made large enough that at least half of it is free. The program text, the compiled code and the symbols are kept to the end. Every block the runner holds is counted against the limit of `-m`.

**Loading.** The library's program text is 48,361,580 bytes in 5,879 lines. Reading it only indexes each define line, by scanning for the names and numbers of arguments of its functions, and keeps the text; a line is read in full and compiled when one of its functions is first called. Measured with `-v` on 2026-11-20 (the command at the end of this section), reading the library and its packages this way took 0.08 seconds of processor time and a peak of 66 MB, nearly all of it the text; with `-l`, which reads and compiles all 6,187 definitions, it took 0.35 seconds and a peak of 224 MB. The runner therefore compiles each definition when it is first called.

**Computing.** A body is compiled to code for a stack machine: a variable is a slot of the frame, an `if` is a jump, a call in the last position of a body reuses the frame, and a lambda application in the last position replaces it. The machine keeps its own stack of return points, so the depth of a program's recursion is bounded by memory and not by the C stack: a recursion a million calls deep runs. The reader, the printer, `equal` and the collector keep their own stacks too, so a datum nested a million levels deep is read and written. Only the compiler recurses in C, once for each level of nesting of a term, and it stops at 10,000 levels; ACL2's library nests well below that, and every definition of the library and of the 460 exported books compiles (the test below). An `attach` line is followed when a call is compiled; of two `define` lines for one function, or two `attach` lines for one, the later is in force (`spec/formats.md`, section 5). The second argument of `(return-last 'mbe1-raw x y)` is checked to be a term and not run.

The measurements of loading come from:

```
echo '(COMMON-LISP::QUOTE 0)' | build/runner/boymoo-run -v -p spec/ground.txt \
  -p build/export/library.statements build/export/library.program
```

and the same with `-l`.

## Where it and ACL2 part

The runner gives ACL2 Core's value. Where ACL2's own evaluator differs, `EDGE-CASES.md` gives the reasons; these are the places a user of the runner meets.

- **Depth.** ACL2 exhausts its stack on a deep recursion (entry 2.6); the runner computes it, in memory.
- **The executable half of an `mbe`** in a function whose guards are verified, which ACL2 runs and the runner does not (entry 2.5).
- **ACL2's own functions in program mode.** ACL2 runs the functions in program mode that it starts with as their Common Lisp code even with guard checking `:none`, where `eq` of two strings with the same characters can be false: `(first-assoc-eq '("") '(("" . -2)))` gives `NIL` in ACL2, and `("" . -2)` by the definitions. A function in program mode defined in a book does not do this (entry 10.2). The tests call such functions within their guards.
- **Speed.** ACL2 computes functions such as `floor`, `mod` and `nonnegative-integer-quotient` with code of the Lisp under it (entry 3.3); the runner runs their definitions, by which `(nonnegative-integer-quotient i j)` subtracts `j` from `i` once for each unit of the quotient.

## Conformance

- **ISO C99** (ISO/IEC 9899:1999), hosted, with no variable-length array, no extension and nothing that the standard leaves undefined or unspecified. It uses only the library of ISO C, and so builds on every system of POSIX.1-2001 and later, whose `c99` is an ISO C99 compiler; it defines no feature-test macro, because it needs nothing of POSIX. It relies on these behaviours that the standard leaves to the implementation:
  1. the characters of the source and of execution are those of ASCII, so that the bytes read can be compared with character constants such as `'('`;
  2. standard input and output, which are text streams, carry every byte unchanged, and a line ends with the byte 10, as POSIX requires;
  3. the statuses 1, 2 and 3 given to `exit` reach the caller as those numbers, as POSIX requires.
- **Evidence.** The machine on which it was written has one C compiler, Apple clang 15.0.0, under the names `cc`, `gcc`, `clang` and `c99`. On 2026-11-20 it built with no diagnostic under `-std=c99 -pedantic-errors -Wall -Wextra -Werror -Wvla -O2` as `cc`, `gcc` and `clang`, and by the `Makefile` as it stands, with `c99 -O 1`, whose driver accepts only the options of POSIX; and `sh runner/test.sh` passed in full both with that build and with a build by `clang` with `-fsanitize=address,undefined -fno-sanitize-recover=all` added to those options.
- **The build and the tests** use the `make` of POSIX.1-2001, POSIX `sh` and POSIX utilities. ACL2 and `python3` are needed only by the tests that compare with ACL2.

## Testing

```
sh runner/test.sh [RUNNER]
```

builds the runner, unless one is named, and compares it with ACL2 8.7. It needs the library's exported files, which it writes with `export/book.sh` if they are missing. It runs:

- the calls of `checks/expected/facts.txt` and of `checks/expected/edge.txt`, lines `value` and `no-value`: the runner must give each value and stop at each call that has none;
- the calls of `runner/test/book.lisp`, a book that ACL2 certifies and the exporter exports: a constrained function with no attachment and one that calls it, an attachment in force, `hard-error` and `illegal` reached and not, a function that is not executable, one introduced by choice, an `mbe`, deep and mutual recursion, a loop, and a function in program mode;
- 2,150 calls of 86 functions of ACL2's library, in logic mode and in program mode, on arguments that `runner/test/gen.py` generates with a fixed seed, run from the library's program text;
- 4,000 calls of the arithmetic primitives on generated integers of up to 120 digits, fractions and complex rationals, and a few arguments that are not numbers;
- cases of the runner alone: a recursion a million calls deep, a term nested a thousand levels deep, one nested twenty thousand levels deep (a stop), a datum nested a million levels deep, numbers of a million digits, memory exhausted by a recursion and by a list under `-m 64`, and texts that are not in the format and terms that are not terms;
- the reading and compiling (`-l`) of every definition of the library and of every book that `export/run.sh` has exported.

ACL2 computes the expected values of the generated calls with `runner/test/expect.lsp`, at its top level, with attachments in force and guard checking `:none`. Run on 2026-11-20, every line was `ok`: 153 values and 4 stops of `facts.txt`, 75 values and 1 stop of `edge.txt`, 11 values and 7 stops of the book, 2,150 library calls and 4,000 arithmetic calls agreed with ACL2, and the program text of the library and of all 460 exported books compiled.

## Benchmarks

```
sh runner/bench.sh [RUNNER]
```

certifies the eleven books of `runner/bench/`, exports them, and times the same call in ACL2 and in the runner. `PLAN.md`, step 3, records the table.
