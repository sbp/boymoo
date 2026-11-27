# The compiler

The compiler of `PLAN.md`, step 7: a program in ACL2 Core that turns ACL2 Core program text into an executable for aarch64, for macOS or for Linux, through a series of small passes: from resolved terms to an SSA intermediate language like QBE's, optimised there, and only in its last passes into A64 instructions. It writes every byte of the executable itself, the code signature that macOS requires included, and uses no assembler, linker or library; the executable makes its system calls directly. The executable computes the 32 primitive functions on every datum, numbers of every kind included, and the five functions of the reference runner's prelude (`runner/README.md`), and gives the values that the reference runner gives with `-j`. ACL2 certifies the compiler; the reference runner runs it once, to compile it; the compiled compiler, compiling its own input, gives its own bytes again.

`compiler/single/` holds the single-pass compiler (`compiler/single/README.md`), which turns each definition straight into assembly items. The reference runner compiles it, its executable is the first to compile the compiler of this directory, and it is the reference with which this compiler's executables are compared. The two compilers share the reader, the index, the data builder, the assembler and the writers of executables, and their executables have the same input, output, exit statuses, data representation and static block. `compiler/DESIGN.md` gives the design of the many-pass compiler: the passes, their languages and the calling convention. This document describes what the two compilers share; how the passes are joined; the back end (passes P6 to P9) and its language MIR in detail; the commands that build, bootstrap, test and measure the compiler; and the results, with what is still missing. Paths are given from the root of the repository, from which every command is run.

## The parts

| File | What it is |
|---|---|
| `DESIGN.md` | The design: the passes, the languages L1, QIR-A, QIR-M and QIR-L, and the calling convention. |
| `package.lsp` | The package `BOYMOO-COMPILER`, in which the books of both compilers are written. |
| `read.lisp` | The reader: it reads the input by position into lines, and decodes strings and symbols written between delimiters. |
| `index.lisp` | The index of definitions and attachments, which also follows attachment chains and lists the primitives and the functions of the prelude. |
| `data.lisp` | The data builder: it lays out the constants, symbols and packages of the program in the static block. |
| `a64.lisp` | The assembler, which turns assembly items into A64 instructions and data, and the tables that the compilers look names up in. It compares two integer or two string keys of its tables directly. |
| `macos.lisp`, `sha256.lisp` | The system routines for macOS, and the writer of the signed Mach-O file, with SHA-256 for its signature. |
| `linux.lisp` | The system routines for Linux, and the writer of the ELF64 file. |
| `runtime.lisp` | The runtime of this compiler, as assembly items: memory and its collector, the primitives, the functions of the prelude, reading and writing. Its collector keeps a nursery that grows with the heap, and collects the old generation in full when it passes a threshold ("The runtime", below). |
| `rt-qir.lisp` | Routines of the runtime written as QIR-M functions (`rt-qir:LENGTH`, `rt-qir:EQUAL` and others), which P4 calls and the back end compiles like any function. |
| `qir.lisp` | What the passes on QIR share: recognisers of well-formed QIR, predecessors, reverse post-order, dominators, liveness, a printer and the table of the runtime's routines. |
| `resolve.lisp` | P1: definitions to L1, resolved terms. |
| `simplify.lisp` | P2: L1 to L1: inlining of small definitions by one rule for all, folding of constants, removal of dead bindings. |
| `lower.lisp` | P3: L1 to QIR-A, SSA form, a self tail call becoming a loop. |
| `expand.lisp` | P4: QIR-A to QIR-M: each primitive expanded into word operations on the data representation, with calls of the runtime for the slow cases. |
| `opt.lisp` | P5: QIR-M to QIR-M: value numbering, folding, removal of dead code, simplification of the graph, sinking, jump threading and loop-invariant code motion. |
| `abi.lisp` | P6: QIR-M to QIR-L: out of SSA form, and the collector's frame. |
| `isel.lisp` | P7: QIR-L to MIR. |
| `rega.lisp` | P8: register assignment on MIR. |
| `emit.lisp` | P9: MIR to assembly items. |
| `compile.lisp` | `COMPILE-TEXT`, which joins the passes. |
| `proofs/` | Proofs about the passes, and `proofs/rega-check.lisp`, the validator of register assignment that the driver runs on every function (`compiler/proofs/README.md`). |
| `build.sh` | Certifies and exports the books. |
| `bootstrap.sh` | Builds the compiler, has the reference runner compile it, has the result compile it again, and compares the two. |
| `compile.sh` | Compiles an input with the compiler on the reference runner. |
| `test.sh` | Compares the executables that this compiler and the single-pass compiler write. |
| `bench/` | Benchmarks of the executables that the two compilers write (`compiler/bench/README.md`). |
| `checker-entry.lisp` | The entry by which the compiled checker reads its five inputs from one string ("The compiled checker", below). |
| `build-checker.sh`, `check.sh`, `frame.sh` | `build-checker.sh` builds the compiled checker; `check.sh` runs it on four files, as `checker/check.sh` runs the checker on the reference runner; `frame.sh` holds the shell function that writes a file as one field of its input. |
| `prover-entry.lisp`, `build-prover.sh` | The framed entry and build command for the executable described in `prover/README.md` ("The compiled prover", below). |
| `decode.sh` | The shell function that turns the string that the reference runner prints into its bytes, for `compiler/compile.sh`, `compiler/single/compile.sh` and `compiler/model/a64-test.sh`. |
| `test-front.sh`, `test-a64.sh`, `test-numbers.sh`, `test-symbols.sh` with `test-symbols.txt`, `test-targets.sh`, `test-checker.sh` | The tests ("Tests", below). |
| `model/` | Models in ACL2 of ACL2 Core and of A64, the machine, with their tests (`compiler/model/README.md`). |
| `single/` | The single-pass compiler: its code generator, `gen.lisp`, its runtime, `runtime.lisp`, `compile.lisp`, which joins its parts, its scripts and its proofs (`compiler/single/README.md`). |

## Building, bootstrapping and testing

```
sh compiler/bootstrap.sh
```

has `compiler/build.sh` certify the books in `build/compiler/acl2/` and export them, and writes the compiler's input `build/compiler/compiler.input`, whose entry is `BOYMOO-COMPILER::COMPILE-TEXT`. The reference runner then runs the compiler on that input, through `compiler/compile.sh` with a limit of 1,024 megabytes, and writes `build/compiler/compiler-1`; `compiler-1` compiles the same input to `build/compiler/compiler-2`. The script prints the time of each step and compares `compiler-1` with `compiler-2`, which must be identical. It needs `acl2`, `build/runner/boymoo-run` and `build/export/library.statements`, and nothing of the single-pass compiler. With `REF=EXECUTABLE`, naming another compiled compiler, such as the single-pass compiler `build/compiler/single/compiler-2` that `sh compiler/single/bootstrap.sh` writes, the script also has that compiler compile the input to `build/compiler/ref-1`, has `ref-1` compile it to `build/compiler/ref-2`, and requires `ref-2` to be `compiler-2` byte for byte. Each executable is written under a temporary name and then renamed, so that a copy still running from an earlier bootstrap is not changed under it (macOS stops a program whose signed file is rewritten in place).

```
sh compiler/compile.sh [-v] [-m MEGABYTES] INPUT > EXECUTABLE
```

compiles an input with the compiler on the reference runner, with its prelude, after `sh compiler/build.sh`; with `-v` the runner also prints its time and peak of memory, and with `-m` it holds at most `MEGABYTES` megabytes (`runner/README.md`).

Beside the compiler's statements and program text, `compiler.statements` and `compiler.program`, `compiler/build.sh` writes `ground.program`, the definitions of the ground theory, and `library.statements`, the lines of ACL2's library that the compiler calls, chosen by `checker/library.awk`. From those lines it leaves out the definitions of `ACL2::HARD-ERROR` and `ACL2::THROW-NONEXEC-ERROR`, as `compiler/single/build.sh` does: ACL2 defines each to return `NIL`, but runs each as an error that ends the computation. With no definition, a call of either stops, as in ACL2; with its definition, it would return `NIL`, and the compiler would go on as if there were no error.

```
build/compiler/compiler-2 < INPUT > EXECUTABLE
```

compiles an input; `chmod +x EXECUTABLE` makes the result executable.

```
sh compiler/test.sh [-q] [--books EXPORT] [--prover INPUT EXPORT] [NEW [REFERENCE]]
```

compiles each of a set of inputs with `NEW` (by default the many-pass compiler, `build/compiler/compiler-2`) and `REFERENCE` (by default the single-pass compiler, `build/compiler/single/compiler-2`), and requires that the two compilers agree on whether they write an executable, and that the two executables give the same standard output, standard error and exit status on each standard input: the single-pass compiler on its own input; the compiled checker on `spec/example` and on every case of `checker/cases/` with a recorded verdict, which must also match the record; the program of `compiler/test-numbers.sh`; `compiler/test-symbols.txt` on the five inputs of `compiler/test-symbols.sh`; and the programs of `compiler/test-front.sh`. With `-q` it leaves out the checker. With `--books EXPORT` it also runs both compiled checkers on every book of `export/books.txt` that `EXPORT/books` holds, with `EXPORT/library.statements` as the library and proofs that skip every obligation, as `compiler/test-checker.sh` checks the books. With `--prover INPUT EXPORT` it compiles `INPUT`, the input of the compiled prover as `compiler/build-prover.sh` writes it, with both compilers, and runs both provers on `spec/example`, on five lines of `EXPORT/library.statements` (each with the lines before it as the library, as `prover/driver/test.sh` forms them), on the first 12 books of `export/books.txt` that `EXPORT/books` holds and on the books of `prover/driver/expected.tsv`, printing the time and the peak of memory of each run and requiring the same output and status. It works in `build/compiler/test`, or in the directory that `COMPILER_TEST_WORK` names, so that two runs at once can be kept apart. It needs the inputs that `sh compiler/single/bootstrap.sh` and `sh compiler/build-checker.sh` write.

## The input and the executable

The input is program text in the format of `spec/formats.md`: the `package` and `hidden-package` lines (section 5), and the `define` and `attach` lines of the program and of every function it calls, those of the ground theory and of ACL2's library included; then one line `(entry NAME)`, which names the function, of one argument, to which the executable gives its standard input; and, for Linux, one line `(target linux)`. As the reference runner does, each compiler takes the last definition and the last attachment of each name.

An optional line `(heap-limit N)` gives the size of each of the copying collector's two spaces in mebibytes (MiB, or 2<sup>20</sup> bytes). `N` is a decimal integer from 1 through 4096. Each compiler accepts one such line. The default is 4096 MiB. The static block, the two stacks, standard input and separately mapped strings each have their own storage, so peak resident memory can exceed this limit.

The executable reads all of its standard input as one string, applies the entry function to it, writes the value, which must be a string, to standard output, and exits with status 0. Where it has no value to write, it writes a line to standard error and exits: with status 1 where there is no value (a call of a function with no definition and no attachment, `pkg-imports`, `pkg-witness` or `symbol-package-name` where they give none, or a value that is not a string), with status 2 where it cannot read its input or write its output, or the package `ACL2` is not declared, and with status 3 where memory is exhausted.

## What the compiler accepts

Each compiler rejects, at compile time, program text that is not in the format, as the reference runner does, and computes from the rest the values that the runner computes. Among the texts that both reject, `test-front.sh` ("Tests", below) checks these:

- a package declared twice with different imports (a package declared more than once is visible if any of its lines is a `package` line);
- a symbol written with a package other than its home package, as `ACL2::CAR` for `COMMON-LISP::CAR`, which `ACL2` imports;
- a string, or a symbol between bars, that escapes a byte that is written as itself;
- a lambda with the same formal twice;
- a formal whose name begins with `&`, or begins and ends with `*`, which the variable rule of `spec/language.md`, section 5, excludes;
- a line `(attach F COMMON-LISP::IF)`, which ACL2 refuses: `IF` is not called with its arguments evaluated;
- a number not in the text of `spec/formats.md`, section 2: an integer with a plus sign, a leading zero or a negative zero; a fraction not in lowest terms, or whose denominator is not above 1; a complex rational whose parts are not so written, or whose imaginary part is 0.

`quote` is recognised only where a term is expected, so that `COMMON-LISP::QUOTE` may be a formal and a variable. An entry function with no definition and no attachment is compiled, and the executable stops when it calls it, as the runner does. A rejected text stops either compiler with status 1 and the line `no value: a call of a function that has no definition and no attachment: ACL2::HARD-ERROR` ("Building, bootstrapping and testing", above), where the runner stops with status 2 and says what is wrong.

## The data

A datum is a word of 64 bits. A reference to an object is its offset in bytes from the base of the heap, which `x28` holds, so that the runtime can copy the static block to the base and use it with no relocation.

| Low bits | Datum |
|---|---|
| `...1` | an integer `n`, from -2<sup>62</sup> to 2<sup>62</sup> - 1, as `2n + 1` |
| `...000` | a cons: the offset of two words, its `car` and its `cdr` |
| `...010` | an object with a header: its offset plus 2 |
| `...100` | a character of code `c`, as `8c + 4` |

An object with a header begins with the word `(size << 8) | type`, where `size` counts the bytes after the header before any padding; objects are aligned to 8 bytes.

| Type | What follows the header |
|---|---|
| 1 | a string: its bytes |
| 2 | a symbol: its name, a string, and the number of its package, an integer |
| 3 | an integer outside the range above: its sign, 0 or 1 for negative, then the digits of its magnitude in base 2<sup>32</sup>, one to a word, the least significant first, the most significant not 0 |
| 4 | a fraction in lowest terms: its numerator and its denominator |
| 5 | a complex rational: its real part and its imaginary part, which is not 0 |
| 6 | a vector: its words |

Every number is held in one way only, so that two numbers are equal exactly when they are held alike.

**The static block** holds the program's constants, the symbols it names and its packages. It stays at the base of the heap and is never moved, and only its word at offset 24 refers to the rest of the heap. Its first words:

| Offset | Word |
|---:|---|
| 0 | the size of the static block in bytes |
| 8 | the package table: entry `p` is a vector of the name of package `p`, its imports and its symbol `ACL2-PKG-WITNESS`, or `NIL` in place of that symbol for a hidden package |
| 16 | the symbol table: a vector of 4,096 buckets, each a list of conses of a key and a symbol |
| 24 | the table of the symbols made while the program runs, a vector, or `NIL` before the first is made; the collector takes this word as a root |
| 32 | the symbol `COMMON-LISP::NIL`, whose datum is therefore 34 |
| 56 | the symbol `COMMON-LISP::T`, whose datum is therefore 58 |

The packages are numbered from 0 in the order of their first declaration, by a `package` or a `hidden-package` line. A symbol is in the bucket of its name in its own package and in that of every package that imports it, under the key of that package: the cons of the package's number and the name. The bucket of a name in package `p`: let `h` be 0, and for each byte `b` of the name let `h` be the low 24 bits of `33h + b`; the bucket is the low 12 bits of `h + 7919p`.

When the input specifies a heap limit, a word holding the limit as an immediate integer follows the symbol buckets at the end of the static block. The runtime distinguishes it by its low bit. A bucket holds an even word, either a cons reference or the datum for `NIL`.

## The runtime

Each compiler has its runtime: `runtime.lisp` here, and `compiler/single/runtime.lisp` for the single-pass compiler. Both provide the routines below, with the same contracts, which `runtime.lisp` gives in a comment before each; they differ in their collectors ("Memory", below).

| Register | Use, once `rt:start` has set up the runtime |
|---|---|
| `x28` | the base of the heap, which never changes |
| `x27`, `x26` | the next free address for objects with a header, and the limit of that address; allocating an object with a header raises `x27`, allocating a cons lowers `x26`, and a collection can change both |
| `x25`, `x24` | the next free word of the value stack and its limit; growing the stack can raise `x24` within a fixed reservation |
| `x23` | the lowest value that `sp` may take in the prologue of a compiled function |
| `x19` to `x22`, `x29` | kept by the routines of the runtime that return |
| `x0` to `x17`, `NZCV` | free across calls of the routines; the runtime states where a routine keeps more |
| `x18` | never used; the system reserves it |
| `sp`, `x30` | the machine stack pointer, a multiple of 16, and the link; a call that returns restores the caller's `sp` and returns through the link it was given |

Compiled functions keep `x23` to `x28` and `sp`; what else they keep, and how they pass arguments and results, is each compiler's own (`compiler/single/README.md`, "The calling convention"; `compiler/DESIGN.md`, section 4).

**The value stack** holds the data of the calls in progress that the collector must see. **The collector** finds every datum in use among the words of the value stack below `x25` and the word at offset 24 of the static block, and moves the objects of the heap outside the static block. A datum that must live across a call, or across a routine that can allocate, is kept on the value stack and loaded again after it: a register keeps its bits, but the object they refer to may have moved. The static block, and strings mapped apart from the heap ("Memory", below), keep their addresses. The words of the machine stack are not roots.

**The routines of the runtime** take their arguments in `x0` onwards and return a datum in `x0`. Those in the table below that return keep `x19` to `x23`, `x25`, `x28`, `x29` and `sp`, and change `x24`, `x26` and `x27` only as the table says. The routines that only the runtime calls have their contracts in `runtime.lisp`, in a comment before each.

**The natives.** The only functions that either compiler computes otherwise than by their definitions are the 32 primitives and the five functions of the prelude listed in `index.lisp`, chosen by name. A call of one of the five computes what the routine `jet:NAME` computes, whatever the program text says of the function, as with the reference runner's `-j`, and a call of a primitive what its routine `prim:NAME` computes, where `NAME` is the symbol as written; each compiler computes some of these calls in the compiled function's own code and makes the rest calls of the routines. No compiler recognises a function of a program by its name or by the shape of its definition and replaces it with other code. Which calls each computes in its own code is its own (`compiler/single/README.md`, "The calling convention"; `compiler/DESIGN.md`, section 3, "QIR-M").

**The program's entry.** `rt:start` copies the static block from the label `data:static`, reads standard input, pushes the string on the value stack, calls the label `rt:entry`, writes the string it returns, and exits. The single-pass compiler gives `rt:entry` to a definition of the entry function (`compiler/single/README.md`, "The calling convention"); this compiler writes `rt:entry` as an adapter that calls the entry function ("P9, emission", below).

The routines that compiled code calls, and their contracts. A primitive or a function of the prelude is named here without its package, which `index.lisp` gives. The free set is `x0` to `x17` and `NZCV`. "Changes" lists what a routine may change apart from its result. A routine that allocates may collect.

| Routine | Takes | Gives in `x0`, or does | Changes | Allocates |
|---|---|---|---|---|
| `prim:BAD-ATOM<=` | two arguments, not read | `NIL` | nothing | no |
| `prim:CAR`, `prim:CDR` | one argument | a field of a cons, or `NIL` | `NZCV` | no |
| `prim:CONSP`, `CHARACTERP`, `STRINGP`, `SYMBOLP`, `INTEGERP`, `RATIONALP`, `COMPLEX-RATIONALP`, `ACL2-NUMBERP` | one argument | `T` or `NIL` | `x1`, `x2`, `NZCV` | no |
| `prim:CHAR-CODE`, `CODE-CHAR` | one argument | a code or a character | `NZCV`, and `x1` for `CHAR-CODE` | no |
| `prim:NUMERATOR`, `DENOMINATOR`, `REALPART`, `IMAGPART` | one argument | a part of a number | `x3` to `x5`, `NZCV` | no |
| `prim:EQUAL` | two arguments | `T` or `NIL` | `x1` to `x12`, `NZCV`, `x24` | no |
| `prim:PKG-IMPORTS`, `PKG-WITNESS` | one argument | the imports or the witness, or a stop | `x1` to `x9`, `NZCV` | no |
| `prim:SYMBOL-NAME`, `SYMBOL-PACKAGE-NAME` | one argument | a string, or a stop | the free set, `x26`, `x27` | only for the empty string given for an argument that is not a symbol |
| `prim:CONS`, `COERCE`, `INTERN-IN-PACKAGE-OF-SYMBOL` | two arguments | a cons, a string or list, or a symbol | the free set, `x24`, `x26`, `x27` | yes |
| `prim:BINARY-+`, `BINARY-*`, `<`, `COMPLEX` | two arguments | a number, or for `<` `T` or `NIL` | the free set, `x24`, `x26`, `x27` | yes |
| `prim:UNARY--`, `UNARY-/` | one argument | a number | the free set, `x24`, `x26`, `x27` | yes |
| `jet:LENGTH` | one argument | a length | `x1` to `x3`, `NZCV` | no |
| `jet:CHAR` | two arguments | a character or `NIL` | `x1` to `x5`, `NZCV` | no |
| `jet:ASH`, `jet:BINARY-LOGXOR` | two arguments | an integer | the free set, `x24`, `x26`, `x27` | yes |
| `jet:SUBSEQ` | three arguments | a string or list | the free set, `x24`, `x26`, `x27` | yes |
| `rt:grow` | in `x0`, the address that the next free word must be able to reach | raises `x24` to cover it, or stops; keeps `x0` | `x8` to `x12`, `NZCV`, `x24` | no |
| `rt:deep` | nothing | stops with status 3 | does not return | no |
| `rt:undefined` | in `x0`, the symbol of a function with no definition | stops with status 1 | does not return | no |
| `rt:alloc` | in `x0`, a number of bytes, a multiple of 8 | the address of that many free bytes | the free set, `x26`, `x27` | yes |
| `rt:stop` | the status in `x0`, and the address and length of a message in `x1` and `x2` | writes the message and a line feed to standard error and exits | does not return | no |
| `rt:start` | the static block | sets up memory, runs the program and exits | does not return | yes |

`prim:CAR`, `prim:CDR` and `prim:CONSP` are part of this interface, although both compilers compute those primitives in the function's own code. The private routine `rt:ensure-stack` takes in `x8` the address that the value stack must reach, keeps `x0` to `x8` and cannot collect; the slow path of `CONS` calls it while its arguments are still in registers, then pushes both before calling `rt:alloc`, and loads them again from the value stack before it writes the cons.

The length in a string's header counts its bytes and not the padding after them. A hidden package has `NIL` in place of its witness in the package table, and its imports are in the symbol table, for interning. The collector copies the digits of an integer of type 3 as bytes, and follows both words of a fraction or a complex rational.

**Symbols made while the program runs.** Interning looks first in the static symbol table, which also resolves imports, and then in the table at offset 24: a vector of the number of its entries and its buckets, each a list of entries that hold a symbol and the hash of its name. A table of 2<sup>k</sup> buckets uses the low `k` bits of the hash of "The data", with the package's number added as there. The table starts with 16 buckets and doubles before an insertion into a full table, placing each entry again by its hash. Through the table, the collector reaches every symbol made and its name, which are never collected.

**Memory.** Each of the two spaces of the collector reserves 4 GiB of addresses by default, or the size specified by `heap-limit`, and the objects of both generations together fit in the capacity of one space. Objects are made in a nursery, objects with a header from one end and conses from the other, within a budget: 1 MiB while the old generation holds less than 128 MiB, and otherwise an eighth of the old generation, up to 32 MiB; always at least the pending request, and at most what the space has left. When the budget is spent, a minor collection copies the objects of the nursery that are in use into the old generation, which grows by bump allocation in the other space, objects with a header from one end and conses from the other. The data of ACL2 Core are never changed after they are made, so an object can refer only to objects older than itself, except in the table of symbols made while the program runs, where interning and the doubling of the table write; the runtime records those writes, and a minor collection takes as roots the value stack, the word at offset 24 of the static block, and the entries of the table so written. A full collection, which copies the old generation into the nursery's space and makes the old generation's space the nursery, follows a minor one when the pending request does not fit, when the old generation has reached its threshold, or, while the old generation holds less than 128 MiB, when the nursery has taken 32 MiB since the last full collection or a request of more than 1 MiB comes while the strings mapped apart take much memory. After a full collection, the threshold is twice the bytes that survived, three halves of them when 128 MiB or more survived, three times them when from 1 to 8 MiB survived and the collection freed at most an eighth of what it copied from, and at least 1 MiB. An allocation that does not fit after a full collection stops with status 3. A collection gives back to the system the pages it used at both ends of the space it leaves, rounded out to 64 KiB. Standard input is read into a mapping of its own, and every string of 256 KiB or more is allocated in one; such strings keep their addresses, and a full collection marks those it reaches, unmaps the rest, and sets a budget for further mappings. The value stack reserves 1 GiB of addresses, and the machine stack is a mapping of 64 MiB.

The runtime of the single-pass compiler copies between two spaces with no generations (`compiler/single/README.md`, "Its runtime's memory").

## Numbers

The numeric primitives compute on integers, fractions and complex rationals, with ACL2's completions: arithmetic takes an argument that is not a number as 0, and the reciprocal of 0 is 0; `complex` takes an argument that is not rational as 0; `<` orders numbers by their real parts, and then by their imaginary parts.

Integers outside the immediate range are added and subtracted digit by digit with a carry or a borrow, and multiplied by the schoolbook method with 64-bit products. Division is long division: the divisor is normalised, and each digit of the quotient is estimated from the two leading digits of the part of the dividend under it; a divisor of one digit uses the machine's division directly. A fraction is reduced by the greatest common divisor, found by Euclid's algorithm of successive remainders. Complex rationals are computed by the rational operations on their parts.

`ash` shifts by whole digits and then by the remaining bits, rounding toward negative infinity on a shift to the right. `binary-logxor` converts the digits to and from two's complement as it goes. Both take an argument that is not an integer as 0. `length` counts the bytes of a string or the conses of a list. `char` and `subseq` take an index that is not a positive integer as 0; `subseq` takes its length from the difference of its end and its start, and a `NIL` end as the length of the sequence.

Arithmetic on immediate integers uses the machine's operations when the result is immediate too. The general routines for integers reserve the storage for their digits with `rt:alloc`, find their operands again after it, and finish the result before they can allocate again; those for fractions and complex rationals keep their intermediate data on the value stack.

## The system

The runtime uses these routines on both systems. Each that returns gives its result in `x0`.

| Routine | What it does |
|---|---|
| `sys:map` | maps the number of bytes in `x0` as zero bytes that can be read and written, and gives their address, or 0 |
| `sys:release` | gives back to the system the pages of the page-aligned address in `x0` and the number of bytes in `x1`, which then read as zero bytes at the same addresses; gives 0, or a negative number on an error |
| `sys:unmap` | removes the mapping at the address in `x0` of the number of bytes in `x1`; gives what `sys:release` gives |
| `sys:read` | reads from the file descriptor in `x0` into the address in `x1` up to the number of bytes in `x2`; gives the number read, or a negative number on an error |
| `sys:write` | writes to the file descriptor in `x0`, from the address in `x1`, up to the number of bytes in `x2`; gives the number written, or a negative number on an error |
| `sys:exit` | ends the process with the status in `x0` |
| `os:main` | the place where the system starts the program, which calls `rt:start` |

On macOS (`macos.lisp`, `SYSTEM-CODE`), a system call is `svc #0x80` with its number in `x16`, and the carry flag shows an error; `sys:release` maps fresh private pages over the range with `MAP_FIXED`. Dyld, the system's loader, starts the program at `os:main`.

On Linux (`linux.lisp`, `LINUX-SYSTEM-CODE`), a system call is `svc #0` with its number in `x8`, and an error is a negative result. `sys:map` calls `mmap` with `MAP_PRIVATE`, `MAP_ANONYMOUS` and `MAP_NORESERVE`: the runtime reserves 8 GiB of addresses by default for its two spaces and touches only the pages it uses, and in its default mode of overcommitting Linux refuses a mapping larger than its memory and swap together unless it is marked so. `sys:release` calls `madvise` with `MADV_DONTNEED`, `sys:unmap` calls `munmap`, and `sys:exit` calls `exit_group`. The kernel starts the program at `os:main` with the program's arguments on the stack.

## The back end

### P6, frames (`abi.lisp`)

`ABI-PROGRAM` takes QIR-M functions to QIR-L functions `(:fn NAME PARAMS BLOCKS NSLOTS)`, whose blocks keep the shape `(LABEL PHIS INSTS JUMP)` with `PHIS` empty. For each function it:

1. makes a conditional jump with two equal targets a jump;
2. splits each edge from a block with two successors to a block with phis, by a new block that jumps to the target;
3. replaces the phis of each block by a parallel copy at the end of each predecessor, made a sequence of `:copy` instructions in which a fresh temporary breaks each cycle;
4. computes the data temporaries live at each point, and finds those live across an instruction that may collect (`qir-inst-may-collect-p`), the spilled temporaries;
5. gives each spilled temporary a slot of the value-stack frame: two spilled temporaries interfere when one is live just after a definition of the other, or both are parameters live on entry, and each takes the lowest slot that no temporary it interferes with has taken;
6. before each instruction that may collect, stores (`(NIL :spill I T)`) each temporary live across it whose slot does not hold its value on every path, and after the instruction loads (`(T :reload I)`) each of them again; a load whose value is not used is then dropped;
7. before each instruction that may collect, sets to the datum 1 (the immediate integer 0) each slot that may hold anything but the value of a temporary live across it: a slot not yet written since the function began (the prologue leaves the frame's words as they were), or one holding a datum whose temporaries are dead, which the collector would otherwise keep alive.

P9 may make the stores, clearing stores and loads around a `:cons` only on the cons's slow path (below), so a `:cons` adds nothing to the set of temporaries whose slot holds their value and takes nothing from the set of slots that may hold a datum, and the loads right after a `:cons` count as uses at the `:cons` when dead loads are dropped. Steps 6 and 7 are forward analyses over the blocks: the set of spilled temporaries whose slot holds their value, which a store adds to, a definition removes from, and the meet of two paths intersects; and the set of slots that may hold something other than the datum 1, every slot on entry, which the meet of two paths unites. After the pass, no data temporary is live across an instruction that may collect, and a temporary is kept in the frame only on the paths that reach such an instruction.

### MIR (`isel.lisp`)

MIR is A64 instructions over registers. A MIR function is `(:mfn NAME PARAMS NSLOTS BLOCKS NEXT)`: `PARAMS` are the registers that hold the parameters on entry, `NSLOTS` the size of the value-stack frame, `NEXT` a number above that of every register, and each block `(LABEL INSTS TERM)` a list of instructions and one terminator. Before P8 a register is a virtual register, a temporary of QIR, `(:d . N)` or `(:w . N)`; after P8 it is a home, `(:x . R)` for the machine register `xR`, or `(:m . K)` for slot `K` of the machine stack. An operand of a call, a tail call or a return may also be a constant `(:k . W)`. `W` below is a word from 0 to 2<sup>64</sup> - 1, and a condition is one of those of the assembly language.

| Instruction | Meaning |
|---|---|
| `(:mov D S)` | `D` := `S` |
| `(:li D W)` | `D` := `W` |
| `(:rrr OP D A B)` | `D` := `A OP B`, `OP` one of `:add-reg :sub-reg :mul :and-reg :orr-reg :eor-reg :lslv :lsrv :asrv` |
| `(:rri OP D A N)` | `D` := `A OP N`: `:add` and `:sub` with `N` from 0 to 4095, `:lsl`, `:lsr` and `:asr` with `N` from 0 to 63, and `:and-mask` with the mask of the low `N` bits |
| `(:cmp A B)`, `(:cmn A B)` | the flags of `A - B` or `A + B` |
| `(:cmpi A N)`, `(:cmni A N)` | the same with `N` from 0 to 4095 |
| `(:cset D C)` | `D` := 1 if `C` holds, else 0 |
| `(:csel D A B C)` | `D` := `A` if `C` holds, else `B`; `A` or `B` may be the constant `(:k . 0)`, written as the zero register |
| `(:tst A N)` | the flags of `A` and the mask of the low `N` bits |
| `(:ld D A N)`, `(:ldb D A N)` | `D` := the word, or the byte, at the heap base plus `A` plus the integer `N` |
| `(:vld D I)`, `(:vst S I)` | load `D` from, or store `S` in, slot `I` of the value-stack frame |
| `(:call F ARGS D)` | call the compiled function `F` with the operands `ARGS`; its result goes in `D`, or nowhere if `D` is `NIL` |
| `(:rt R ARGS D)` | the same for the routine of the runtime with the label `R`; a call of `prim:COMMON-LISP::CONS` has a fifth field, the registers that the loads right after it load, which count as its uses |

| Terminator | Meaning |
|---|---|
| `(:b L)` | go to block `L` |
| `(:bc C L1 L0)` | go to `L1` if `C` holds of the flags set by the last instruction of the block, else to `L0` |
| `(:cbnz A L1 L0)` | go to `L1` if `A` is not 0, else to `L0` |
| `(:tbnz A N L1 L0)` | go to `L1` if bit `N` of `A` is 1, else to `L0` |
| `(:ret A)` | return `A` |
| `(:tail F ARGS)` | return the value of the call of `F` with `ARGS` |
| `(:undef W)` | stop with status 1 for the function whose symbol has the word `W` |

### P7, instruction selection (`isel.lisp`)

`ISEL-PROGRAM` takes each instruction of QIR-L to MIR. A constant that an instruction needs in a register is loaded into a new word temporary by `:li`. An addition or subtraction of a constant whose word, or whose negation, is below 4096 takes the immediate form, as does a shift by a constant and a conjunction with a mask of low bits; the operands of a commutative operation are swapped to put a constant second. A comparison sets the flags with `:cmp`, `:cmpi` or `:cmni` (swapping its operands and its condition to put a constant second); `:ovadd` and `:ovsub` set them by `:cmn` and `:cmp`, whose overflow flag is that of the addition or subtraction, with the condition `:vs`. The pass follows which comparison the flags hold within a block: a selection or a `:jnz` whose condition is that comparison's temporary reads the flags (`:csel`, `:bc`), and a comparison all of whose uses do so gets no `:cset`. A selection on any other word compares it with 0, and later selections on the same word reuse those flags. A conjunction with a mask of low bits whose only use is a comparison with 0 later in the block becomes `:tst`; a test of bit 0 that a `:jnz` reads becomes `:tbnz`, in a function of fewer than 1,000 instructions, so that the branch stays within its range. A `:jnz` otherwise becomes `:cbnz`. `:cons` becomes a call of the routine `prim:COMMON-LISP::CONS`.

### P8, register assignment (`rega.lisp`)

`REGA-ALLOCATION` computes, for one function, the virtual registers live on entry to each block, and gives each virtual register one interval: with the instruction of index `I`, counting from 1 in the order of the blocks, reading its sources at `2I` and writing its destination at `2I + 1`, and the parameters written at 1, the interval spans every place at which the register is defined, used, or live on entry to or exit from a block. The kinds of a register: one live across a `:call` must live in a slot of the machine stack, since a call of a compiled function may change every register; one live across a `:rt` only may get `x19` to `x22` or `x29`, which every routine keeps; one stored just before or loaded just after a call of `prim:COMMON-LISP::CONS` is kept out of `x0` and `x1`; any other gets one of `x0` to `x15`, `x19` to `x22` and `x29`.

Before the scan, the two sides of each copy between virtual registers are coalesced, given one home, when neither is live just after a definition of the other (the copy itself included) and neither crosses a call (at most 256 copies are tried in a function); the copy then moves a register to itself and is dropped. Linear scan visits the intervals of the groups in order of their start; when no register is free, the interval with the furthest end among the active ones and the new one goes to a slot of the machine stack. Slots are reused once their intervals have ended, except that a register put out of its register by a later one takes a new slot. A group is first offered the registers of its hints that are free: the registers of the virtual registers it is copied to or from, then `xI` for the `I`-th parameter, `xI` for an argument of a call or tail call, from 0 to 7, and `x0` for the result of a call and the operand of a return.

`REGA-APPLY` replaces each virtual register by its home, and drops a move from a register to itself; `REGA-FUNCTION` is the two together. The driver calls `REGA-VALIDATED-PROGRAM` of `proofs/rega-check.lisp` instead, which checks each assignment (every register has a home, the live-in sets are a fixed point, no two registers live at once share a home, and each register live across a call is in a home that the call keeps) before applying it, and stops the compiler if a check fails. `x16` and `x17` are never assigned: P9 uses them.

### P9, emission (`emit.lisp`)

`EMIT-PROGRAM` writes assembly items. The frame of a function:

| | |
|---|---|
| Machine stack | when the function calls (a `:call` or `:rt`, or a tail call with more than eight arguments) or has slots of its own: `FRAME` bytes, 16 for the link at `[sp]` and 8 for each slot `K` at `[sp, 8 + 8K]`, rounded up to a multiple of 16, checked against `x23` (`rt:deep`) |
| Value stack | `NSLOTS` words above the arguments; with the arguments that its calls push on the value stack, checked against `x24` by `rt:ensure-stack`, which takes the required address in `x8` and keeps `x0` to `x8`; `x25` is raised over them, and P6 makes sure each is stored or cleared before anything can collect |
| Parameters | the first eight from `x0` to `x7`, the rest from the value stack below the frame, moved to their homes: first those whose home is a slot, then the parallel moves between registers, then those on the value stack |

A call of `prim:COMMON-LISP::CONS` is written inline, as the routine's own fast path is: when `x26 - x27` leaves 16 bytes, the next cons address, kept at `x28 - 112`, and `x26` go down by 16, and the two data in `x0` and `x1` are stored there; otherwise a slow path after the function's code calls the routine and comes back.

Slot `I` of the value-stack frame is at `x25 - 8(NSLOTS - I)`. A call stores its arguments after the eighth at `x25` upward and raises `x25` over them, moves the first eight into `x0` to `x7` by a parallel move (with `x16` to break a cycle), calls, and moves `x0` to the home of its result. A return moves its operand into `x0`, lowers `x25` by the frame and the arguments on the value stack, restores the link and `sp`, and returns. A tail call puts its arguments after the eighth above `x25`, its first eight in `x0` to `x7`, copies the first group down to the place of the caller's own arguments, sets `x25` above them, removes the machine frame and jumps. A function that makes no call and has no slot has no frame. Blocks are laid out in their order, and a jump to the next block is left out; a conditional jump whose second target is next becomes one conditional branch, and one whose first target is next the opposite branch.

Further, P9:

- writes a function whose only calls are of routines, with no slots of either stack and nothing passed on the value stack, with no frame: it keeps its link on the machine stack around each such call;
- writes the arguments of an inline cons that are in registers straight from them, and its result straight into its home, leaving the moves into `x0` and `x1` to the slow path;
- moves the stores just before an inline cons and the loads just after it to the cons's slow path, when no stored or loaded home is `x0` or `x1` and no loaded home is that of the result: the fast path cannot collect and leaves those homes as they were;
- leaves out a block other than the first that has no instruction and only jumps, and sends every jump to it to its target;
- puts the calls of `rt:deep` and `rt:ensure-stack` after the function's code, so that a prologue whose checks pass takes no branch;
- leaves out the check of `sp` against `x23` in a function that is on no cycle of the call graph, when every chain of calls from it through such functions takes at most 8 KiB of the machine stack, half the 16 KiB that the runtime keeps below `x23`. A cycle is found, in a search of the call graph, as an edge to a function on the search's path, whose target is then made to check; so every cycle has a function that checks.

`EMIT-ENTRY-ADAPTER` writes `rt:entry`: it takes the argument that `rt:start` pushed on the value stack into `x0`, removes it, calls the entry function, and returns to `rt:start`.

## The assembly language

The code generators of both compilers and the runtimes write assembly items, lists that `a64.lisp` lays out, finding the place of every label, and then writes as bytes. A register is a number from 0 to 31: 31 is `sp` in `:mov-sp`, `:add` and `:sub` and as the base of a load or a store, and the zero register elsewhere; an immediate form that sets the flags and has 31 as its source takes it as 0, in two instructions. A condition is one of `:eq :ne :hs :lo :mi :pl :vs :vc :hi :ls :ge :lt :gt :le :al`. Labels are compared with `equal`: the code generators use `(:fn NAME)` for a function and a list for a place within one. The assembler rejects a label defined twice or not at all, and a field out of its range.

| Item | Meaning, on 64-bit registers |
|---|---|
| `(:label L)` | the place `L` |
| `(:movz rd imm16 shift)`, `(:movk ...)`, `(:movn ...)` | with `shift` 0, 16, 32 or 48 |
| `(:mov rd rm)` | `orr rd, xzr, rm` |
| `(:mov-sp rd rn)` | `add rd, rn, #0`, to or from `sp` |
| `(:add rd rn imm12)`, `(:sub ...)`, `(:adds ...)`, `(:subs ...)` | with `imm12` from 0 to 4095 |
| `(:cmp rn imm12)`, `(:cmn rn imm12)` | the flags of a subtraction or an addition |
| `(:add-reg rd rn rm sh)`, `(:sub-reg ...)`, `(:adds-reg ...)`, `(:subs-reg ...)` | with `rm` shifted left by `sh` |
| `(:cmp-reg rn rm)`, `(:neg rd rm)` | a comparison of two registers; a negation |
| `(:and-reg rd rn rm)`, `(:orr-reg ...)`, `(:eor-reg ...)`, `(:ands-reg ...)`, `(:tst-reg rn rm)`, `(:mvn rd rm)` | bitwise operations on registers |
| `(:and-mask rd rn k)`, `(:tst-mask rn k)` | with the mask of the low `k` bits, `k` from 1 to 63 |
| `(:lsl rd rn n)`, `(:lsr ...)`, `(:asr ...)` | shifts by `n` |
| `(:lslv rd rn rm)`, `(:lsrv ...)`, `(:asrv ...)` | shifts by a register |
| `(:clz rd rn)` | the number of leading zero bits of `rn` |
| `(:mul rd rn rm)`, `(:smulh rd rn rm)`, `(:sdiv rd rn rm)`, `(:udiv rd rn rm)`, `(:msub rd rn rm ra)` | a product, the high half of a signed product, a signed or unsigned quotient, and `ra` less a product |
| `(:csel rd rn rm cond)`, `(:cset rd cond)` | a choice of register by the flags; 1 or 0 by the flags |
| `(:ldr rt rn off)`, `(:str rt rn off)` | with `off` a multiple of 8 from 0 to 32760 |
| `(:ldr-reg rt rn rm)`, `(:str-reg rt rn rm)` | at the address `rn + rm` |
| `(:ldrb rt rn off)`, `(:strb ...)`, `(:ldrb-reg rt rn rm)`, `(:strb-reg ...)` | one byte, with `off` from 0 to 4095 |
| `(:ldur rt rn off)`, `(:stur ...)`, `(:ldurb ...)` | a word, or a byte, at `rn + off`, with `off` from -256 to 255 |
| `(:ldp rt rt2 rn off)`, `(:stp ...)` | with `off` a multiple of 8 from -512 to 504 |
| `(:ldp-post rt rt2 rn off)`, `(:stp-pre rt rt2 rn off)` | the same, writing back `rn` |
| `(:b L)`, `(:bl L)`, `(:b-cond cond L)`, `(:cbz rt L)`, `(:cbnz rt L)` | to a label |
| `(:tbz rt bit L)`, `(:tbnz rt bit L)` | to `L` when bit `bit` of `rt` is 0, or is 1, with `bit` from 0 to 63 and `L` within 32 KiB |
| `(:adr rd L)` | the address of `L`, within a megabyte |
| `(:adr-far rd L)` | the address of `L`, by `adrp` and `add` |
| `(:br rn)`, `(:blr rn)`, `(:ret)`, `(:svc imm16)` | a branch or a call through a register, a return, a system call |
| `(:bytes S)` | the bytes of the string `S`, then zero bytes to a multiple of 4 |
| `(:quad N)` | a word of 64 bits, the least significant byte first |
| `(:image SIZE FRAGMENTS)` | `SIZE` bytes, held as a list of strings in order |

Of these, only the many-pass compiler writes `:ldur`, `:stur`, `:ldurb`, `:tbz` and `:tbnz`. In the package `BOYMOO-COMPILER`, `(A64-ASSEMBLE ITEMS ENTRY)` gives the bytes as a string and the offset of the label `ENTRY` as two values; `(A64-ASSEMBLE-IMAGE ITEMS ENTRY)` gives the bytes as an image, their number with a list of strings in order, and that offset; and `(A64-BYTES ITEMS)` gives the bytes alone. The code begins on a boundary of 4,096 bytes in the executable, which `:adr-far` relies on.

## The driver (`compile.lisp`)

`COMPILE-TEXT` reads the input, indexes it and lays out the static block as `compile-text` does in `compiler/single/compile.lisp`, and makes the definition of the entry as `compile-entry-definitions` does. P1 (`resolve-definitions`) resolves every definition, and P2's analysis (`simplify-analyze`, `simplify-inlinees`) chooses the definitions to inline, from the whole program. Then each definition in turn goes through P2, P3 (`lower-def`), P4 (`expand-fn`), P5 (`opt-function`), P6, P7 and P8 with its validation, and only its MIR with homes is kept; the routines of `rt-qir.lisp` follow, from P5 on. P9 then writes every function, and the executable holds the system's routines, the runtime, `rt:entry`, the compiled functions and the static block, assembled and written as by the single-pass compiler. `COMPILE-TEXT-WITH` takes two more arguments, which leave out P2 and P5; `*SIMPLIFY-ENABLED*` and `*OPTIMIZE-ENABLED*`, both true, are those that `COMPILE-TEXT` gives.

## The executable files

**For macOS**, `macos.lisp` writes a Mach-O file for arm64 that dyld loads as position-independent code. Its three segment commands reserve `__PAGEZERO`, map `__TEXT` to be read and run and `__LINKEDIT` to be read. The code starts at offset 4,096 in the file, and `__TEXT` is filled with zero bytes to a multiple of 16,384 bytes. `LC_MAIN` gives the entry, `LC_DYLD_INFO_ONLY` empty streams of relocations, bindings and exports, and `LC_LOAD_DYLINKER` the loader; the file names no library. `LC_CODE_SIGNATURE` locates the signature in `__LINKEDIT`: a SuperBlob holding one ad-hoc CodeDirectory, with a SHA-256 hash of each page of 4,096 bytes of the file before the signature, the header and padding included. The fields of Mach-O are little-endian, and those of the signature big-endian. The writer gives an empty string if the entry is not a multiple of 4 within the code or the offset of the signature does not fit in 32 bits.

**For Linux**, `linux.lisp` writes an ELF64 file of type `ET_EXEC` for `EM_AARCH64`, in the little-endian formats of the System V Application Binary Interface and of *ELF for the Arm 64-bit Architecture (AArch64)*. Its one `PT_LOAD` segment maps the whole file at the address `0x400000`, to be read and run, aligned to 64 KiB. The code starts at offset `0x1000` in the file, and the entry is at `0x401000` plus its offset in the code. The file has no section table, interpreter, dynamic section or signature. The writer gives an empty string if the entry is not a multiple of 4 within the code.

## Tests

Each test compares a compiler with the reference runner, the system's tools, or a fixed expectation, and prints what it found. All need `build/runner/boymoo-run`. `test-front.sh` and `test-targets.sh` with no argument use the many-pass compiler, `build/compiler/compiler-2`, which `sh compiler/bootstrap.sh` makes; `test-numbers.sh`, `test-front.sh` with `--reference` and `test-symbols.sh` with no argument use the single-pass compiler on the reference runner, `compiler/single/compile.sh`, which needs what `sh compiler/single/build.sh` writes; `test-a64.sh` and `test-checker.sh` build what they need. A compiled compiler named as the argument of `test-front.sh`, `test-symbols.sh` or `test-targets.sh` takes the place of the default.

- `sh compiler/test-front.sh [--reference | COMPILER]` runs the reference runner and the compiler on each case of "What the compiler accepts", runs the executable when one is made, and compares the statuses and values.
- `sh compiler/test-a64.sh` certifies and exports the assembler alone, with `sh compiler/single/build.sh --a64`, and compares the bytes of its test items, among which is an instance of each instruction of "The assembly language", with those of the system assembler, `clang -arch arm64 -c`, read with `otool`.
- `sh compiler/test-numbers.sh` compiles one program that computes every numeric primitive and the jets on a fixed set of operands, among them the bounds of the immediate integers, 2<sup>64</sup>, 2<sup>128</sup>, fractions, complex rationals and data that are not numbers, with a collection in the midst of the arithmetic, and compares the text of its results with the reference runner's. `compiler/test.sh` gives the same program to both compiled compilers.
- `sh compiler/test-symbols.sh [COMPILER]` compiles `test-symbols.txt`, which interns 4,000 names, two with the same hash, and interns each again, and asks about imports, witnesses and hidden packages, and compares the results with the reference runner's.
- `sh compiler/test-targets.sh [COMPILER]` compiles a program that gives back its input, for macOS and for Linux, checks the headers of both files with `od` and `awk` and the signature with `codesign -v --strict`, and runs the macOS executable. When `docker` reaches a running Colima, it also makes a local image that holds only the Linux executable, with `docker import` from a `tar` archive, runs it with no network and a root that cannot be written, and removes the image; otherwise it says so and skips that run.
- `sh compiler/test-checker.sh` is described under "The compiled checker", below.

`compiler/single/README.md`, "Test results", gives the results of these tests with the single-pass compiler. On 2026-11-27, `sh compiler/test-a64.sh` printed `A64 assembler agrees with the system assembler on 304 bytes.`

## The compiled checker

`checker-entry.lisp` defines the entry of the checker of `PLAN.md`, step 4, as an executable. Its standard input holds five strings, each after its length in bytes as four bytes, the most significant first: the ground theory, the library, the statements, the proofs and the library's proofs. It gives them to `BOYMOO::CHECK-FOUR` and writes the verdict and a line feed, or `invalid checker input frame` and a line feed if the input is not five such strings.

```
sh compiler/build-checker.sh
COMPILER=EXECUTABLE sh compiler/build-checker.sh
sh compiler/check.sh LIBRARY STATEMENTS PROOFS [LIBRARY-PROOFS]
```

`build-checker.sh` has `checker/build.sh` build the checker, has ACL2 certify the entry beside the checker's books and the exporter export it, writes the compiler's input, `build/compiler/checker-test/checker.input`, and compiles it to `build/compiler/checker`. The variable `COMPILER` chooses the compiler: unset or empty, the many-pass compiler, `build/compiler/compiler-2`, compiles the input, and the script first runs `sh compiler/bootstrap.sh` when that executable is missing or older than a book of the compiler; set to a compiled compiler, such as the single-pass compiler, `build/compiler/single/compiler-2`, that executable compiles it. `check.sh` takes the arguments of `checker/check.sh`, gives the compiled checker `spec/ground.txt` and the four files as its five strings, and writes the verdict line; unlike `checker/check.sh`, it writes no second line saying what failed in a rejection.

The library check of `PLAN.md`, step 6, gives the compiled checker the library as the first input, the second and third empty, and the library's proofs as the fourth:

```
: > build/empty
sh compiler/check.sh build/export/library.statements build/empty build/empty build/prover/library.proofs
```

`compiler/single/README.md`, "The compiled checker", gives its time and memory with the checker that the single-pass compiler writes, and "Results", below, compares the checkers that the two compilers write.

`sh compiler/test-checker.sh [N]` builds the compiled checker with `build-checker.sh`, with the compiler that `COMPILER` names, and runs it, and the checker on the reference runner, on `spec/example` and on every case of `checker/cases/` and `checker-js/cases/` whose verdict is recorded, comparing the verdicts with each other and with the record. Then it runs the compiled checker on each book of `export/books.txt` that has been exported, with proofs that skip every obligation, as `checker/books.sh` does, and the reference runner on the first `N` of them, 20 if `N` is not given. It writes each result to `build/compiler/checker-test/results.tsv`, and the books with no export to `build/compiler/checker-test/missing-books.txt`. It exits with status 1 if a book has no export, if the compiled checker stops on an input, or if, on an input with a reference run, the compiled checker's verdict, the reference runner's and the recorded one are not all the same. It needs `acl2`, `timeout` and `zsh`, whose `time` measures each run, and runs on macOS.

`compiler/single/README.md`, "The compiled checker", gives the result of `sh compiler/test-checker.sh 460` with the checker that the single-pass compiler writes.

## The compiled prover

`prover-entry.lisp` defines the entry of the prover's driver as an executable, which reads its inputs as framed fields as the compiled checker does (`prover/README.md`, "Executable driver").

```
sh compiler/build-prover.sh
COMPILER=EXECUTABLE sh compiler/build-prover.sh
```

needs `sh prover/build-all.sh` to have been run. It has ACL2 certify the entry beside the driver's books and the exporter export it, writes the compiler's input, `build/compiler/prover-build/prover.input`, from the definitions that the entry reaches, with the heap limit that `PROVER_HEAP_LIMIT` gives in MiB, 1024 by default, and compiles it to `build/compiler/prover`. The variable `COMPILER` chooses the compiler: unset or empty, the many-pass compiler, `build/compiler/compiler-2`, compiles the input, and the script first runs `sh compiler/bootstrap.sh` when that executable is missing or older than a book of the compiler; set to a compiled compiler, such as the single-pass compiler, `build/compiler/single/compiler-2`, that executable compiles it. The executable is `build/compiler/prover` either way, which `PROVER_DRIVER=compiled` has the prover's scripts run.

## Results

All of the following were run on 2026-11-27 on Apple silicon, on a machine doing other work, one at a time; times are elapsed seconds and memory the most bytes resident under `/usr/bin/time -l`, unless said otherwise. Both compilers compile the same program text, and every pair of executables gave the same output, error output and status, except where said.

**Bootstrap.** `sh compiler/bootstrap.sh` had the reference runner compile the compiler in 77.17 s (65.27 s of the runner's processor time, with 891 definitions compiled, 215 collections and at most 104,174 KB held, by the runner's own count), and `compiler-1` compile the same input in 2.13 s to the same 1,816,448 bytes. With `REF=build/compiler/single/compiler-2`, it also printed `The compiler compiled by build/compiler/single/compiler-2 writes compiler-2 again, byte for byte.`

**Tests.** `sh compiler/test-a64.sh` printed `A64 assembler agrees with the system assembler on 304 bytes.` `sh compiler/test-front.sh`, `sh compiler/test-numbers.sh`, which printed `Numeric primitives and jets agree on 16281 bytes of results.`, `sh compiler/test-symbols.sh build/compiler/compiler-2`, which found the two programs agreeing on all five of its comparisons, `sh compiler/test-targets.sh`, which checked both files' headers and the signature and ran the macOS executable and, in Colima, the Linux one, `sh compiler/model/core-test.sh` and `sh compiler/model/a64-test.sh` passed. `sh compiler/test.sh` printed `Compared 417 compilations and runs of build/compiler/compiler-2 with build/compiler/single/compiler-2; 0 differed.` `sh compiler/test.sh --books EXPORT`, with `EXPORT` a directory holding the exports of all 460 books of `export/books.txt`, printed `Books checked by both checkers: 460.` and `Compared 877 compilations and runs of build/compiler/compiler-2 with build/compiler/single/compiler-2; 0 differed.` `COMPILER=build/compiler/compiler-2 sh compiler/test-checker.sh 460` printed `Reference runner matched 1233 expected verdicts on 1233 inputs in 1059.69 s elapsed, 565641216 bytes peak RSS.` and `Compiled checker, same 1233 inputs: 103.17 s elapsed.` With the prover that this compiler writes, `PROVER_TEST_JOBS=1 sh prover/test-all.sh --compare` printed `All prover tests passed.`

**The library check.** With the checker that `sh compiler/build-checker.sh` writes, `sh compiler/check.sh build/export/library.statements build/empty build/empty build/prover/library.proofs` gave `accepted` in 13.25 s and 12.85 s, with at most 331,808,768 bytes resident; with the checker that `COMPILER=build/compiler/single/compiler-2 sh compiler/build-checker.sh` writes, in 25.18 s, with at most 336,740,352 bytes.

**The same programs compiled by both compilers**, measured with `sh compiler/bench/run.sh` and `sh compiler/bench/prover.sh PROVER-INPUT EXPORT misc/dft-ex build/choice misc/hidden-defpkg-checks/top arithmetic/equalities std/basic/arith-equivs` (`compiler/bench/README.md`), the prover's input written as `compiler/build-prover.sh` writes it:

| Program and input | Executable written by the single-pass compiler | Executable written by the many-pass compiler |
|---|---:|---:|
| the single-pass compiler on its own input | 0.41 s, 35,848,192 | 0.18 s, 20,119,552 |
| the compiled checker on the library check | 23.33 s, 352,288,768 | 13.06 s, 331,808,768 |
| the single-pass compiler on the input of the compiled prover | 20.95 s, 1,314,439,168 | 8.97 s, 591,544,320 |
| the compiled prover on `misc/dft-ex` | 258.16 s, 1,206,419,456 | 137.07 s, 1,129,086,976 |
| the compiled prover on `std/basic/arith-equivs` | 394.17 s, 969,342,976 | 206.00 s, 794,116,096 |
| the compiled prover on `arithmetic/equalities` | 73.18 s, 880,492,544 | 43.92 s, 628,129,792 |
| the compiled prover on `build/choice` | 23.03 s, 757,858,304 | 13.02 s, 641,007,616 |
| the compiled prover on `misc/hidden-defpkg-checks/top` | 26.56 s, 876,118,016 | 14.86 s, 581,615,616 |

In the third line both executables wrote the same prover, byte for byte, and on each book the two provers wrote the same proofs. Of the four small programs of `compiler/bench/`, the one of arithmetic takes 2,146,304 bytes resident with this compiler against 1,163,264, the size of its first allocation budget; the other three take no more memory than with the single-pass compiler.

**The prover on other inputs.** `sh compiler/test.sh --prover PROVER-INPUT EXPORT` found the two provers giving the same proofs, byte for byte, and the same status on `spec/example`, on lines 7, 19, 39, 57 and 1492 of the library (each with the lines before it as the library), and on `build/outer`, `misc/defpun`, `misc/defpm`, `std/alists/alist-equiv`, `clause-processors/ev-theoremp`, `std/system/defchoose-queries`, `misc/hidden-defpkg-checks/top`, `build/choice`, `arithmetic/equalities`, `misc/dft-ex`, `misc/expander`, `sorting/how-many`, `arithmetic-5/lib/basic-ops/distributivity` and `std/strings/strsplit`. On `std/basic/arith-equivs` the single-pass compiler's prover did not finish within that script's limit of 300 s, where the many-pass compiler's prover took 213.92 s; with no limit, as above, the two give the same proofs.

**The compiler itself.** `sh compiler/build-prover.sh` compiled the prover in 62.52 s, with at most 1,357,037,568 bytes resident in the whole build. The prover that this compiler writes is 36,029,312 bytes, against 23,876,480 for the one that the single-pass compiler writes. Measured in ACL2 on `build/compiler/compiler.input`, the passes that allocate most are P5 (703 MB), P8 (341 MB), P6 (214 MB) and P4 (118 MB).

## What is missing

- **The many-pass compiler's own speed and memory on huge inputs.** On the prover's input the many-pass compiler takes three times as long as the single-pass compiler, 62.52 s against 20.95 s ("Results": the third line of the table is the single-pass compiler compiling that input), and more memory. The time goes mostly to collection, driven by the allocation of P5, P8 and P6; the peak follows the size of the code being assembled, which is half as large again as the single-pass compiler's, because the assembler holds every item of the program at once. A streaming assembler, and fewer rebuilt maps in P5 and P8, are the next steps.
- **Large proofs.** `std/basic/arith-equivs` takes 206 s with the prover that the many-pass compiler writes and 394 s with the single-pass compiler's, both well beyond the other books measured.
- **Code size.** Inline expansions of primitives and inlining make executables larger than those of the single-pass compiler (36 MB against 24 MB for the prover).
