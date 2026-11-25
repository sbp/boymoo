# The fast runner

The fast runner is the reference runner of `runner/` made faster for development work. It takes the same arguments as `boymoo-run`, reads the same files and standard input, and must give the same standard output and the same exit status. Before it computes, it translates the definitions that the terms on standard input can reach into C, compiles them with the system's C compiler, keeps the objects in a cache named by a hash of their text, and loads them; everything else is the reference runner's own code.

Nothing trusts it. No result of the repository depends on it, and wherever its output matters the reference runner is the judge: `sh runner-fast/test.sh` compares the two, and a difference is a bug in the fast runner.

Paths below are given from the root of the repository, from which every command is run.

## Building

```
make -f runner-fast/Makefile
```

writes `build/runner-fast/boymoo-run-fast`. The `Makefile` is for the `make` of POSIX.1-2001 and calls the compiler as `cc`, with `-std=c99 -O2 -Wall -Wextra`; `CC`, `CFLAGS`, `LDFLAGS`, `LIBS` (default `-lpthread`) and `OUT`, the directory written, may be given on the command line. Of the reference runner's sources, it compiles `runner/heap.c` and `runner/prelude.c` and includes `runner/run.h` and `runner/prelude.h` as they are; `eval.c`, `sys.c`, `num.c` and `data.c` are in this directory, each the reference runner's file of that name with the differences listed under "How it works", point 5.

The fast runner needs more than ISO C99, in these places:

- `jit.c` uses POSIX: `posix_spawn` and `wait` to run the compiler, `realpath`, `mkdir` and `stat`, and `dlopen` and `dlsym` to load the compiled code; `sys.c` uses POSIX threads.
- `num.c` uses the type `__int128`, and `fastrt.h`, which the compiled code includes too, uses `__builtin_frame_address` and `__attribute__((musttail))`. These are extensions of C that Clang provides.
- `jit.c` links the compiled code into a shared library with the options `-dynamiclib -undefined dynamic_lookup`, which are those of the compiler and linker of macOS.

## Running

```
build/runner-fast/boymoo-run-fast [-l] [-v] [-j] [-m megabytes] [-p packages] ... program ...
```

The arguments, the input, the output, the stops and their statuses are those of `runner/README.md`. With `-j` it starts with the reference runner's prelude, five functions that it computes by the same code, `runner/prelude.c` and the reference runner's `ash` and `binary-logxor`, which `num.c` holds too; a define line for one of them is read and not used. They have no define line, so they are never compiled nor inlined: the interpreter runs each as one instruction, and compiled code calls it through its entry. The messages of a stop name the program as `boymoo-run`, as the reference runner's do; only the standard output and the status are meant to be the same. With `-v`, the times of reading and of computing leave out the time spent preparing compiled code, which `BOYMOO_FAST_VERBOSE` reports.

The first run that reaches a definition compiles it, which costs the time of the compiler (for the call of `runner/bench/library.lisp`, under "Speed", about 1.2 seconds of processor time more than a run that finds it in the cache); a later run that reaches the same definitions finds them in the cache and calls no compiler.

The places it uses are found when it runs, from the root of the repository. The root is the value of `BOYMOO_FAST_ROOT`, or the current directory if that is not set. The C it writes includes `fastrt.h` from `ROOT/runner-fast` and `run.h` from `ROOT/runner`, and the cache is `ROOT/build/runner-fast/cache`, which it makes if it is missing. If the root, the two headers or the cache cannot be found, or the compiler or the loading fails, the run is left to the interpreter, which gives the same values more slowly.

| Variable | Effect |
|---|---|
| `BOYMOO_FAST_ROOT=DIR` | The root of the repository (default: the current directory). |
| `BOYMOO_FAST_CACHE=DIR` | The cache (default: `build/runner-fast/cache` under the root). |
| `BOYMOO_FAST=0` | Nothing is compiled and no native function is used: the interpreter runs everything, with the changes to `num.c` and `data.c` of point 5. |
| `BOYMOO_FAST_NATIVE=0` | The native functions (below) are not used, and their definitions run, compiled. |
| `BOYMOO_FAST_NOINLINE` | When set, to any value, no call is inlined in the C written. The C differs, and so do its names in the cache. |
| `BOYMOO_FAST_VERBOSE` | When set, to any value but `0`: on standard error, the number of functions reached and of units, the bytes of C written, every command run, the fingerprint of each native function's definition, and the time taken. |
| `BOYMOO_FAST_KEEP` | When set, to any value: the C files written for a compilation are kept in `obj/tmpPID` in the cache, `PID` being the number of the process. |
| `BOYMOO_FAST_NAMES` | When set, to any value: each C function written is given the name of its definition, with every character that a C name may not hold written as `_`, so that a profile by a sampler of the system names the definitions. The C differs, and so do its names in the cache. |

## How it works

The sources of this directory are `eval.c`, `sys.c`, `num.c` and `data.c` (point 5); `gen.c`, which writes C from the machine's code; `jit.c`, which finds the definitions to compile, writes their C into the cache, runs the compiler and loads the result; `native.c`, the native functions; `fastrt.h`, what the compiled C sees of the runner; and `fast.h`, the declarations that the files of the runner share.

1. **Which functions.** Standard input is read whole before the first term is computed, and then taken line by line exactly as the reference runner takes it. Every word of it that names a defined function starts a closure: each function in it is built, that is, read and compiled to the stack machine's code as at its first call, and every function its code calls is added. A definition that cannot be built, because it is not a term or its line is not in the format, is left unbuilt, and the stop that building it caused is caught, so that the interpreter stops at its call where the reference runner stops.
2. **C for each function, from the machine's code** (`gen.c`). The depth of the operand stack is known at every operation, so every slot is `stk[fp + n]` with `n` a number written into the C. The frame stays on the reference runner's own value stack, below its top at every point at which memory can be collected, so the collector finds and moves every datum in use as it does for the interpreter. A jump is a `goto`; a call is a C call; a call of the function itself in the last position is a jump to its start, and any other call in the last position is a tail call that does not grow the C stack (`musttail`). The primitives `car`, `cdr`, `cons`, `equal`, the recognizers, and `+`, `*`, unary `-` and `<` on immediate integers are done inline, by the machine's own fast paths; every other case calls the reference runner's code for the primitive. A call of a function whose code has at most 48 words is replaced by that code, to a depth of 3, unless it is one of the native functions. Constants that are symbols, conses or boxes, and the functions called, are found by their ordinal in the function's code, through tables that are filled when the code is loaded, so that the C depends only on the shape of the code.
3. **Deep recursion.** The work runs on a thread with a stack of 256 MB. Before every call that is not in the last position, the compiled code compares its stack pointer with a floor 4 MB above the end of that stack; below the floor, the call, and everything under it, runs in the interpreter, whose stacks are in the heap and counted against `-m`. If the thread cannot be made, the work runs on the first thread, whose stack is taken to be 8 MB.
4. **The cache.** The unit of compilation is a define line. The C of each unit is named by a hash of 128 bits of its text and of a stamp, and compiled once, to `obj/HASH.o` in the cache, by `cc -O2 -w -fPIC`, in batches of up to 200 units, or of about 1,500,000 bytes of C, to a command, two commands at a time. The objects of a run are linked into `set/HASH.dylib`, named by a hash of the stamp and the names of its units, and loaded; the loading checks the name of every function of every unit and the numbers of its constants and calls against the code built in this process before it fills any table. Files are written into a folder of the process and then renamed into place, so that runs at the same time never see half of a file. The stamp is a hash of the text of `runner-fast/fastrt.h` and `runner/run.h`, read when the runner runs, and of the compiler's options: these, with the C itself, are all that the compiled code depends on. A change to either header changes every name in the cache; the fast runner itself must then be built again, which the `Makefile` does, since both headers are among its prerequisites. The key does not cover the compiler: after a change of `cc`, empty the cache. The cache is never emptied by the runner.
5. **The differences of the four files from the reference runner's.**
   - `eval.c` declares the machine's code, its operations and the table of functions in `fast.h`, to share them with `gen.c` and `jit.c`. It keeps a table of entry points, one for each function, which runs the function in the interpreter until compiled code replaces it. The machine is a function that runs until it returns to a given point, so that compiled code can call the interpreter and the interpreter compiled code; at a call it uses the callee's entry point when the callee has compiled or native code and the C stack is above the floor. It adds `try_build`, which builds a definition and, at a stop, leaves it unbuilt, and functions by which compiled code calls a primitive and grows the value stack.
   - `sys.c` reads standard input whole before the first term, prepares the compiled code unless `BOYMOO_FAST=0`, and then takes the input line by line as the reference runner does, reading each line where it lies, and lets the input go once its last line is read. It runs the work on the thread of point 3. Its `stop` returns to `try_build` when that is building a definition, and otherwise stops as the reference runner's does.
   - `num.c` adds, multiplies and compares integers and fractions whose numerator and denominator are below 10<sup>18</sup> in magnitude in machine words, with products of 128 bits and Euclid's algorithm in 64 bits, and holds nothing in the heap until the result is complete. A result that does not fit is left to the reference runner's code. Every rational has one representation, so the result is the one that code gives. It adds three functions for the native forms: `num_quotient`, the quotient of integers rounded down; `num_bits`, the four bitwise operations on integers below 2<sup>127</sup> in magnitude, by numbers of 128 bits; and `num_shift`, the shift of such an integer; a result is written in the heap in the one representation of its value.
   - `data.c`: `equal` passes over a part that is the same object on both sides without comparing it or putting it on its stack.

## The native functions

Some functions of ACL2's library are defined by a recursion whose depth is a property of the data rather than of the work: the length of a string, the size of a quotient, the number of bits of an integer. The runner holds strings, integers and their arithmetic directly, so `native.c` computes eleven such functions itself, on the arguments on which the answer is plain, and on any other arguments runs the definition. Under `-j` five of them, `length`, `char`, `subseq`, `binary-logxor` and `ash`, are the prelude's, which computes them for every argument, and their native forms are not used.

**Strings.** ACL2 defines `length`, `char`, `subseq`, `string-append` and `string<`, and through `string<` also `string>`, `string<=` and `string>=`, on a string through the list of the string's characters, so that each call takes time in proportion to the length of the string, and a loop over the characters of a string takes time in proportion to the square of its length. The runner holds a string's length and its bytes.

**The quotient.** ACL2 defines `nonnegative-integer-quotient` by taking the divisor from the dividend until less than the divisor is left: a recursion as deep as the quotient, through which `floor`, `mod`, `truncate` and `rem` compute. The runner divides, by the reference runner's division of integers of any size.

**Bitwise operations.** ACL2 defines `binary-logand`, `binary-logior`, `binary-logxor` and `binary-logeqv`, and through them `lognand`, `logorc1`, `logandc1` and `lognor`, one bit at a time, with a call of `floor`, and so a division, at each bit. The runner applies the machine's operation to integers that fit in 128 bits.

**The shift.** ACL2 defines `ash` as the floor of an integer times a power of two, and makes that power by one multiplication for each bit of the shift. The runner shifts an integer that fits in 128 bits.

| Function | Answered natively when |
|---|---|
| `COMMON-LISP::LENGTH` | its argument is a string. |
| `COMMON-LISP::CHAR` | its arguments are a string and an integer `n` with 0 ≤ `n` < the length of the string. |
| `COMMON-LISP::SUBSEQ` | its arguments are a string, an integer `start` and an integer `end`, with 0 ≤ `start` ≤ `end` ≤ the length of the string, or `nil` for `end`, which then stands for the length. |
| `ACL2::STRING-APPEND` | its arguments are two strings. |
| `COMMON-LISP::STRING<` | its arguments are two strings. |
| `ACL2::NONNEGATIVE-INTEGER-QUOTIENT` | its arguments are integers `i` ≥ 0 and `j` > 0, of any size. |
| `ACL2::BINARY-LOGAND`, `ACL2::BINARY-LOGIOR`, `ACL2::BINARY-LOGXOR`, `ACL2::BINARY-LOGEQV` | its arguments are two integers below 2<sup>127</sup> in magnitude. The result, in two's complement of unbounded width, as ACL2 defines these functions, is then at most 2<sup>127</sup> in magnitude; the machine's operation on numbers of 128 bits gives it. |
| `COMMON-LISP::ASH` | its arguments are integers `i` and `c`, with `i` and the result below 2<sup>127</sup> in magnitude and `c` below 2<sup>29</sup> in magnitude. |

A native form is used only when the program text defines the function, and every function its code can reach, by exactly the lines expected. The **fingerprint** of a function is a hash of 128 bits of the text of those lines, in the order in which a walk of the code first meets them; the table in `native.c` records the fingerprint of each of the eleven, and a native form is installed only when the fingerprint found is the one recorded. A native function is never inlined, so that every call of it goes through its entry point. One that makes a datum first sets the top of the value stack to the end of its own arguments, so that the collector, if it runs inside it, finds every datum that its callers hold. The native forms are installed with the compiled code, and so not under `BOYMOO_FAST=0`, nor when compiling fails.

The fingerprints recorded are those of the library's program text, `build/export/library.program`, as `sh export/run.sh` writes it under ACL2 8.7:

| Function | Fingerprint |
|---|---|
| `COMMON-LISP::LENGTH` | `632dc9c397cbb009240d46cf8e2ab594` |
| `COMMON-LISP::CHAR` | `a0554e87125b22c19dc46ac38aa64e4a` |
| `COMMON-LISP::SUBSEQ` | `1221e857a158a5c30bb8a0efeb59eb2a` |
| `ACL2::STRING-APPEND` | `44eec3995eec702248f747c6d482accf` |
| `ACL2::NONNEGATIVE-INTEGER-QUOTIENT` | `cfb4342f75aff8574f436865d8877d71` |
| `ACL2::BINARY-LOGAND` | `89f95ced204ab156ca96f8e51114db87` |
| `ACL2::BINARY-LOGIOR` | `c0ac0a436880002e14b242357f3113dc` |
| `ACL2::BINARY-LOGXOR` | `e2dec0d955011f0df5916518bfe3ed80` |
| `ACL2::BINARY-LOGEQV` | `8f1604a273296d8d521930d76bcd0cbd` |
| `COMMON-LISP::STRING<` | `a74f29ac7bf90202d803bc986070ccd5` |
| `COMMON-LISP::ASH` | `78faf3eae3110cd72f08e499a84c408e` |

This command prints, for each, the fingerprint found, the one expected, and whether the native form is used:

```
echo '(COMMON-LISP::LENGTH (COMMON-LISP::QUOTE "a"))' |
  BOYMOO_FAST_VERBOSE=1 build/runner-fast/boymoo-run-fast -p spec/ground.txt \
    -p build/export/library.statements build/export/library.program 2>&1 >/dev/null |
  grep fingerprint
```

On 2026-11-23 it printed, for each of the eleven, the fingerprint of the table and `native`.

## Testing

```
sh runner-fast/test.sh
```

builds the fast runner, and the reference runner if it is not up to date, and compares the two on the inputs below; it needs no ACL2, but reads files that `sh runner/test.sh` and `sh checker/build.sh` write, which must have been run first. Its cache of compiled code is `build/runner-fast/test/cache`. It prints one line for each set and ends with `all fast runner tests passed` or `some fast runner tests failed`.

`runner-fast/test/gen.awk`, a program for the `awk` of POSIX, writes the calls of four of the sets, which it names `arith`, `natives`, `large` and `loop`. Each set has a fixed seed, and the numbers are drawn by a generator written in the file, not by `rand`, in whole numbers that every awk computes exactly, so that the calls are the same on every run and under every awk. On 2026-11-23, the awk of macOS 14.4.1 (version 20200816) and GNU Awk 5.3.2, as `gawk` and as `gawk --posix`, wrote the same four files: for each set, `awk -v set=SET -f runner-fast/test/gen.awk | cksum` printed the same under each.

The reference runner cannot be the judge of the sets `large` and `loop`, which the definitions do not finish, so there the judge is ACL2. `runner-fast/test/expected/large.txt` and `loop.txt` hold ACL2's value of each call, one a line, in 88,719 and 136,885 bytes, and the fast runner must print those files. `sh runner-fast/test/record.sh`, which needs ACL2 and stops under any version but that of `checks/version.lsp`, records them again: ACL2 reads the calls that `gen.awk` writes, writes each back in the text of `spec/formats.md`, which must give the same bytes, and evaluates each as its top level does, with guard checking `:none`. Run on 2026-11-23 with ACL2 8.7, it printed `ok` for both sets. `cksum.txt`, beside the two files, holds what `cksum` prints for the calls that were recorded, and the test requires the same of the calls it writes, so that an awk that wrote other calls would be reported as that, and not as a wrong value.

Run on 2026-11-25, with the compiled definitions of earlier runs still in the cache, it printed `ok` for every line and ended with `all fast runner tests passed`, in 92 seconds of elapsed time. Every line below compares standard output and exit status:

| Set | Result |
|---|---|
| The reference runner's cases, as `sh runner/test.sh` last wrote them: the calls of `checks/expected/facts.txt` and `edge.txt`, of `runner/test/book.lisp`, of 86 functions of the library and of the arithmetic primitives, and, under `-j`, of the five functions of the prelude and of `ash` and `binary-logxor` on large integers, each file whole and each call that has no value alone | 153 and 4, 75 and 1, 11 and 7, 2,150, 4,000, 3,349 and 996 terms: the same |
| The reference runner's cases of the runner alone: a recursion a million calls deep, terms nested a thousand and twenty thousand levels deep, a datum nested a million levels deep, numbers of a million digits, memory exhausted by a recursion and by a list under `-m 64`, 26 texts that are not in the format or terms that are not terms, three program texts that stop (one with no newline at its end, one whose definition uses a variable that is not bound, called after a term that has a value, and one that defines a primitive), `-l` and `-l -j` on the library, and the functions of the prelude called from a term and from a definition, without `-j`, with it, and with it and define lines for `ash` and `char` | the same, with statuses 0, 0, 2, 0, 0, 3 and 3, then 2 for each text and each program text, 0 for `-l` and `-l -j`, and 1, 0 and 0 |
| 20,000 calls of `binary-+`, `binary-*`, `<`, `unary--` and `unary-/` on integers and fractions near 2<sup>29</sup>, 10<sup>9</sup>, 2<sup>32</sup>, 10<sup>18</sup> and 2<sup>63</sup>, every fraction in lowest terms | the same, with status 0 |
| 10,000 calls of the eleven native functions, and of `string>`, `string<=`, `string>=`, `floor`, `mod`, `truncate`, `rem`, `lognand`, `logorc1`, `logandc1` and `lognor` through them, on which the definitions finish, about a quarter of them on arguments outside those of the native forms: native, with `BOYMOO_FAST_NATIVE=0`, and on the reference runner | the same three ways, with status 0 |
| 4,000 calls of `nonnegative-integer-quotient`, `floor`, `mod`, `truncate`, `rem`, the four bitwise functions and `ash` on integers of up to 200 bits, on which the definitions do not finish, and so neither the reference runner nor `BOYMOO_FAST_NATIVE=0` can be run: the native values against ACL2's, in `runner-fast/test/expected/large.txt`, and each, by `equal`, against the integer read from its text, which holds only when the native form writes the one representation of its value | all 4,000 the same, and all equal |
| 12 calls of `explode-nonnegative-integer` on integers of 4,000 digits, of `logcount` on integers of 4,000 bits and of `string-append-lst` on a thousand strings, which call the native quotient and `string-append` again and again while they hold data of their own, with memory collected many times inside the native functions: the values against ACL2's, in `runner-fast/test/expected/loop.txt` | the same |
| The eleven native forms installed for `build/export/library.program` | all eleven |
| The checker, `BOYMOO::CHECK`, on the 772 cases of `checker/cases/` and `checker-js/cases/` | the same |
| The checker's reader of its inputs, `BOYMOO::TEXT-LINES`, on five texts: empty, without a final line feed, with empty lines and a return, and every byte | the same |
| A recursion ten million calls deep, which goes below the floor of point 3 and is finished in the interpreter | `10000000` from both |

## Speed

```
sh runner-fast/bench.sh
```

has ACL2 certify and the exporter export the eleven books of `runner/bench/` into `build/runner-fast/bench/` and `build/export/books/build/runner-fast/bench/`, unless that is done already, and runs the call `(bench-BOOK)` of each in both runners: the whole process, which reads the library's program text and the book's and makes the call. The fast runner runs it once first, so that its code is in its cache. Times are seconds of processor time, user and system, medians of three runs; the ratio is the reference runner's time over the fast runner's, and both runners must give the same output and status. Run on 2026-11-23:

| Book | Reference runner | Fast runner | Ratio | Value |
|---|---:|---:|---:|---|
| `fib` | 0.40 | 0.13 | 3.1 | same |
| `loop` | 1.19 | 0.23 | 5.2 | same |
| `lists` | 0.85 | 0.22 | 3.9 | same |
| `sort` | 0.94 | 0.22 | 4.3 | same |
| `alist` | 0.50 | 0.14 | 3.6 | same |
| `fact` | 0.16 | 0.15 | 1.1 | same |
| `power` | 0.69 | 0.67 | 1.0 | same |
| `fractions` | 0.14 | 0.12 | 1.2 | same |
| `chars` | 0.76 | 0.24 | 3.2 | same |
| `symbols` | 0.35 | 0.17 | 2.1 | same |
| `library` | 1.44 | 0.23 | 6.3 | same |

Every process includes the reading of the library's program text, 48,361,580 bytes, so a call that computes for a small fraction of a second is bounded by it. `fact`, `power` and `fractions` spend their time in arithmetic on large integers, which is the reference runner's code in both.

The first run of `library` with an empty cache, which compiles its 35 units, 81,114 bytes of C, took 1.64 seconds of elapsed time and 1.43 of processor time, the compiler's included; the second took 0.22 and 0.22. Measured on 2026-11-23 with:

```
echo '(ACL2::BENCH-LIBRARY)' |
  BOYMOO_FAST_CACHE=build/runner-fast/empty-cache BOYMOO_FAST_VERBOSE=1 env time -p \
    build/runner-fast/boymoo-run-fast -p spec/ground.txt -p build/export/library.statements \
    -p build/export/books/build/runner-fast/bench/library.statements \
    build/export/library.program build/export/books/build/runner-fast/bench/library.program
```

run twice, after `sh runner-fast/bench.sh` and with no folder `build/runner-fast/empty-cache`.

## What it was tested on

Everything above was run on one machine, under macOS 14.4.1 on an Apple M1, with Apple clang 15.0.0 as `cc`, both to build the fast runner and to compile the code it writes. It has been built and run on no other system and with no other compiler; the options it gives the linker are those of macOS.

## What is not done

- It has not been built or run on any system other than macOS, nor with any compiler other than Apple clang.
- The address and undefined-behaviour sanitizers, under which the reference runner's tests have passed, have not been run on it.
- The term on each line of standard input is run by the interpreter, which then calls the compiled code; only definitions are compiled.
- The cache is never emptied, and its key does not cover the compiler.
