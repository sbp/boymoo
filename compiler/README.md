# The compiler

The compiler of `PLAN.md`, step 7: a program in ACL2 Core that turns ACL2 Core program text into an executable for aarch64, for macOS or for Linux. It writes every byte of the executable itself, the code signature that macOS requires included, and uses no assembler, linker or library; the executable makes its system calls directly. The executable computes the 32 primitive functions on every datum, numbers of every kind included, and the five functions of the reference runner's prelude (`runner/README.md`), and gives the values that the reference runner gives with `-j`. The reference runner runs the compiler once, to compile the compiler; the compiled compiler, compiling its own input, gives its own bytes again.

Paths below are given from the root of the repository, from which every command is run.

## The parts

| File | What it is |
|---|---|
| `package.lsp` | The package `BOYMOO-COMPILER`, in which the compiler's books are written. |
| `read.lisp` | The reader: it reads the input by position into lines, and decodes strings and symbols written between delimiters. |
| `index.lisp` | The index of definitions and attachments, which also follows attachment chains and lists the primitives and the functions of the prelude. |
| `data.lisp` | The data builder: it lays out the constants, symbols and packages of the program in the static block. |
| `gen.lisp` | The code generator: it turns each definition into assembly items. |
| `a64.lisp` | The assembler, which turns assembly items into A64 instructions and data, and the tables that the compiler looks names up in. |
| `runtime.lisp` | The runtime, as assembly items: memory and its collector, the primitives, the functions of the prelude, and reading and writing. |
| `macos.lisp`, `sha256.lisp` | The system routines for macOS, and the writer of the signed Mach-O file, with SHA-256 for its signature. |
| `linux.lisp` | The system routines for Linux, and the writer of the ELF64 file. |
| `compile.lisp` | `COMPILE-TEXT`, which joins the parts. |
| `checker-entry.lisp` | The entry by which the compiled checker reads its five inputs from one string ("The compiled checker", below). |
| `build-checker.sh`, `check.sh`, `frame.sh` | `build-checker.sh` builds the compiled checker; `check.sh` runs it on four files, as `checker/check.sh` runs the checker on the reference runner; `frame.sh` holds the shell function that writes a file as one field of its input. |
| `build.sh` | Has ACL2 certify the compiler's books and the exporter export them. |
| `compile.sh`, `decode.sh` | `compile.sh` compiles an input on the reference runner; `decode.sh` holds the shell function that turns the string that the runner prints into its bytes. |
| `bootstrap.sh` | Builds the compiler, has the reference runner compile it, has the result compile it again, and compares the two. |
| `test-front.sh`, `test-a64.sh`, `test-numbers.sh`, `test-symbols.sh` with `test-symbols.txt`, `test-targets.sh`, `test-checker.sh` | The tests ("Tests", below). |
| `model/` | Models in ACL2 of ACL2 Core and of A64, the machine, with their tests (`compiler/model/README.md`). |

## Building and running

```
sh compiler/build.sh
```

has ACL2 certify the compiler's books in `build/compiler/acl2/`, and the exporter write the compiler's statements and program text as `build/compiler/compiler.statements` and `build/compiler/compiler.program`. Beside them it writes `ground.program`, the definitions of the ground theory, and `library.statements`, the lines of ACL2's library that the compiler calls, chosen by `checker/library.awk`. From those lines it leaves out the definitions of `ACL2::HARD-ERROR` and `ACL2::THROW-NONEXEC-ERROR`: ACL2 defines each to return `NIL`, but runs each as an error that ends the computation. With no definition, a call of either stops, as in ACL2; with its definition, it would return `NIL`, and the compiler would go on as if there were no error. The script needs `acl2`, `build/runner/boymoo-run` and `build/export/library.statements`.

```
sh compiler/bootstrap.sh
```

builds the compiler, writes its input, `build/compiler/compiler.input`, and has the reference runner compile it to `build/compiler/compiler-1`, a macOS executable, which compiles the same input to `build/compiler/compiler-2`. It prints the time of each and compares the two byte for byte. Run on 2026-11-25 on Apple silicon, the reference runner took 20.62 s (19.577 s of processor time, with a peak of 28,720 KB of memory held), and `compiler-1` took 0.43 s; the two executables were identical, of 974,336 bytes. `/usr/bin/time -l build/compiler/compiler-2 < build/compiler/compiler.input > /dev/null`, run three times on the same day, took from 0.40 s to 0.43 s, with at most 20,365,312 bytes resident.

```
sh compiler/compile.sh [-v] INPUT > EXECUTABLE
build/compiler/compiler-2 < INPUT > EXECUTABLE
```

compile an input on the reference runner, with its prelude, and with the compiled compiler; with `-v` the runner also prints its time and peak of memory. `chmod +x EXECUTABLE` makes the result executable.

## The input and the executable

The input is program text in the format of `spec/formats.md`: the `package` and `hidden-package` lines (section 5), and the `define` and `attach` lines of the program and of every function it calls, those of the ground theory and of ACL2's library included; then one line `(entry NAME)`, which names the function, of one argument, to which the executable gives its standard input; and, for Linux, one line `(target linux)`. As the reference runner does, the compiler takes the last definition and the last attachment of each name.

The executable reads all of its standard input as one string, applies the entry function to it, writes the value, which must be a string, to standard output, and exits with status 0. Where it has no value to write, it writes a line to standard error and exits: with status 1 where there is no value (a call of a function with no definition and no attachment, `pkg-imports`, `pkg-witness` or `symbol-package-name` where they give none, or a value that is not a string), with status 2 where it cannot read its input or write its output, or the package `ACL2` is not declared, and with status 3 where memory is exhausted.

## What the compiler accepts

The compiler rejects, at compile time, program text that is not in the format, as the reference runner does, and computes from the rest the values that the runner computes. Among the texts that both reject, `test-front.sh` ("Tests", below) checks these:

- a package declared twice with different imports (a package declared more than once is visible if any of its lines is a `package` line);
- a symbol written with a package other than its home package, as `ACL2::CAR` for `COMMON-LISP::CAR`, which `ACL2` imports;
- a string, or a symbol between bars, that escapes a byte that is written as itself;
- a lambda with the same formal twice;
- a number not in the text of `spec/formats.md`, section 2: an integer with a plus sign, a leading zero or a negative zero; a fraction not in lowest terms, or whose denominator is not above 1; a complex rational whose parts are not so written, or whose imaginary part is 0.

`quote` is recognised only where a term is expected, so that `COMMON-LISP::QUOTE` may be a formal and a variable. An entry function with no definition and no attachment is compiled, and the executable stops when it calls it, as the runner does. A rejected text stops the compiler with status 1 and the line `no value: a call of a function that has no definition and no attachment: ACL2::HARD-ERROR` ("Building and running", above), where the runner stops with status 2 and says what is wrong.

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

## The calling convention

| Register | Use, once `rt:start` has set up the runtime |
|---|---|
| `x28` | the base of the heap, which never changes |
| `x27`, `x26` | the next free address for objects with a header, and the limit of that address; allocating an object with a header raises `x27`, allocating a cons lowers `x26`, and a collection can change both |
| `x25`, `x24` | the next free word of the value stack and its limit; growing the stack can raise `x24` within a fixed reservation |
| `x23` | the lowest value that `sp` may take in the prologue of a compiled function |
| `x19` to `x22`, `x29` | kept by compiled functions and by the routines of the runtime that return |
| `x0` to `x17`, `NZCV` | free across calls; a compiled call returns its datum in `x0`; the runtime states where a routine keeps more |
| `x18` | never used; the system reserves it |
| `sp`, `x30` | the machine stack pointer, a multiple of 16, and the link; a call that returns restores the caller's `sp` and returns through the link it was given |

**The value stack** holds the arguments and the live data of every call in progress. A compiled function of `n` arguments finds them in the `n` words below `x25`, may push words above them, and returns with `x25` lowered by `8n`. A call in the last position of a body moves its arguments to the place of the caller's own, restores the machine frame and jumps, so that a recursion in the last position takes no room on either stack. The prologue calls `rt:deep` if its frame of 16 bytes on the machine stack would go below `x23`, and `rt:grow` if its frame on the value stack would pass `x24`.

**The collector** finds every datum in use among the words of the value stack below `x25` and the word at offset 24 of the static block, and moves the objects of the heap outside the static block. A datum that must live across a call, or across a routine that can allocate, is kept on the value stack and loaded again after it: a register keeps its bits, but the object they refer to may have moved. The static block, and strings mapped apart from the heap ("The runtime", below), keep their addresses. The words of the machine stack are not roots.

**The routines of the runtime** take their arguments in `x0` onwards and return a datum in `x0`. Those in the table of "The runtime" that return keep `x19` to `x23`, `x25`, `x28`, `x29` and `sp`, and change `x24`, `x26` and `x27` only as the table says. The routines that only the runtime calls have their contracts in `runtime.lisp`, in a comment before each.

The generator computes `CAR`, `CDR` and `CONSP` in the function's own code, always; `IF` as a comparison of its test with `NIL`, the datum 34; `EQUAL` where the two words are the same or one is an immediate integer or a character; and `BINARY-+`, `UNARY--` and `<` of two immediate integers whose result is one. Every other call of a primitive is a call of its routine, `prim:NAME`, where `NAME` is the primitive's symbol as written; a call of one of the five functions of the prelude listed in `index.lisp`, chosen by name, is a call of `jet:NAME`, whatever the program text says of the function, as with the reference runner's `-j`.

**The program's entry** is the label `rt:entry`, which the compiler gives to the definition of the entry function; when that function has an attachment, is computed by the runtime, or has no definition, the compiler makes a definition that calls it, and gives the label to that. `rt:start` copies the static block from the label `data:static`, reads standard input, pushes the string, calls `rt:entry` as a compiled function, writes the string it returns, and exits.

## The runtime

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

`prim:CAR`, `prim:CDR` and `prim:CONSP` are part of this interface, although the generator computes those primitives in the function's own code. The private routine `rt:ensure-stack` takes in `x8` the address that the value stack must reach, keeps `x0` to `x8` and cannot collect; the slow path of `CONS` calls it while its arguments are still in registers, then pushes both before calling `rt:alloc`, and loads them again from the value stack before it writes the cons.

The length in a string's header counts its bytes and not the padding after them. A hidden package has `NIL` in place of its witness in the package table, and its imports are in the symbol table, for interning. The collector copies the digits of an integer of type 3 as bytes, and follows both words of a fraction or a complex rational.

**Symbols made while the program runs.** Interning looks first in the static symbol table, which also resolves imports, and then in the table at offset 24: a vector of the number of its entries and its buckets, each a list of entries that hold a symbol and the hash of its name. A table of 2<sup>k</sup> buckets uses the low `k` bits of the hash of "The data", with the package's number added as there. The table starts with 16 buckets and doubles before an insertion into a full table, placing each entry again by its hash. Through the table, the collector reaches every symbol made and its name, which are never collected.

**Memory.** Each of the two spaces of the copying collector reserves 4 GiB of addresses. Objects with a header grow from one end of the active space and conses from the other, under one budget, which a collection sets to the largest of 64 KiB, twice the bytes that survived, and the bytes that survived together with the request pending, up to 4 GiB; a request beyond that stops with status 3. A collection gives back to the system the pages it used at both ends of the space it leaves, rounded out to 64 KiB. Standard input is read into a mapping of its own, and every string of 256 KiB or more is allocated in one; such strings keep their addresses, and a collection marks those it reaches, unmaps the rest, and sets a budget for further mappings. The value stack reserves 1 GiB of addresses, and the machine stack is a mapping of 64 MiB.

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

On Linux (`linux.lisp`, `LINUX-SYSTEM-CODE`), a system call is `svc #0` with its number in `x8`, and an error is a negative result. `sys:map` calls `mmap` with `MAP_PRIVATE`, `MAP_ANONYMOUS` and `MAP_NORESERVE`: the runtime reserves 8 GiB of addresses for its two spaces and touches only the pages it uses, and in its default mode of overcommitting Linux refuses a mapping larger than its memory and swap together unless it is marked so. `sys:release` calls `madvise` with `MADV_DONTNEED`, `sys:unmap` calls `munmap`, and `sys:exit` calls `exit_group`. The kernel starts the program at `os:main` with the program's arguments on the stack.

## The assembly language

The code generator and the runtime write assembly items, lists that `a64.lisp` lays out, finding the place of every label, and then writes as bytes. A register is a number from 0 to 31: 31 is `sp` in `:mov-sp`, `:add` and `:sub` and as the base of a load or a store, and the zero register elsewhere; an immediate form that sets the flags and has 31 as its source takes it as 0, in two instructions. A condition is one of `:eq :ne :hs :lo :mi :pl :vs :vc :hi :ls :ge :lt :gt :le :al`. Labels are compared with `equal`: the generator uses `(:fn NAME)` for a function and a list holding a serial number for a place within one. The assembler rejects a label defined twice or not at all, and a field out of its range.

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
| `(:ldp rt rt2 rn off)`, `(:stp ...)` | with `off` a multiple of 8 from -512 to 504 |
| `(:ldp-post rt rt2 rn off)`, `(:stp-pre rt rt2 rn off)` | the same, writing back `rn` |
| `(:b L)`, `(:bl L)`, `(:b-cond cond L)`, `(:cbz rt L)`, `(:cbnz rt L)` | to a label |
| `(:adr rd L)` | the address of `L`, within a megabyte |
| `(:adr-far rd L)` | the address of `L`, by `adrp` and `add` |
| `(:br rn)`, `(:blr rn)`, `(:ret)`, `(:svc imm16)` | a branch or a call through a register, a return, a system call |
| `(:bytes S)` | the bytes of the string `S`, then zero bytes to a multiple of 4 |
| `(:quad N)` | a word of 64 bits, the least significant byte first |
| `(:image SIZE FRAGMENTS)` | `SIZE` bytes, held as a list of strings in order |

In the package `BOYMOO-COMPILER`, `(A64-ASSEMBLE ITEMS ENTRY)` gives the bytes as a string and the offset of the label `ENTRY` as two values; `(A64-ASSEMBLE-IMAGE ITEMS ENTRY)` gives the bytes as an image, their number with a list of strings in order, and that offset; and `(A64-BYTES ITEMS)` gives the bytes alone. The code begins on a boundary of 4,096 bytes in the executable, which `:adr-far` relies on.

## Between the parts

`COMPILE-TEXT` takes the input as a string and gives the executable as a string:

1. `READ-PROGRAM` reads the input into its lines.
2. `INDEX-LINES` finds the last definition and the last attachment of each name, the package lines, the entry and the target; `RESOLVE-ATTACHMENTS` follows the chains of attachments and rejects a cycle.
3. `DATA-BUILD` lays out the static block, and gives the table from the text of each constant to its datum. `COMPILE-ENTRY-DEFINITIONS` makes a definition for the entry when the entry's function has an attachment, is a routine of the runtime, or has no definition.
4. `COMPILE-ITEMS` puts together the system's routines, `(SYSTEM-CODE)` or `(LINUX-SYSTEM-CODE)`, the runtime's, `(RUNTIME-CODE)`, the compiled functions, which `GEN-FUNCTIONS` writes from the definitions, the arities, the attachments and the table of constants, and last the static block at the label `data:static`.
5. `A64-ASSEMBLE-IMAGE` assembles them, and gives the image and the offset of `os:main` in it.
6. `MACHO-IMAGE-EXECUTABLE` or `ELF-IMAGE-EXECUTABLE` writes the executable from the image and that offset. `MACHO-EXECUTABLE` and `ELF-EXECUTABLE` do the same from the bytes as one string.

## The executable files

**For macOS**, `macos.lisp` writes a Mach-O file for arm64 that dyld loads as position-independent code. Its three segment commands reserve `__PAGEZERO`, map `__TEXT` to be read and run and `__LINKEDIT` to be read. The code starts at offset 4,096 in the file, and `__TEXT` is filled with zero bytes to a multiple of 16,384 bytes. `LC_MAIN` gives the entry, `LC_DYLD_INFO_ONLY` empty streams of relocations, bindings and exports, and `LC_LOAD_DYLINKER` the loader; the file names no library. `LC_CODE_SIGNATURE` locates the signature in `__LINKEDIT`: a SuperBlob holding one ad-hoc CodeDirectory, with a SHA-256 hash of each page of 4,096 bytes of the file before the signature, the header and padding included. The fields of Mach-O are little-endian, and those of the signature big-endian. The writer gives an empty string if the entry is not a multiple of 4 within the code or the offset of the signature does not fit in 32 bits.

**For Linux**, `linux.lisp` writes an ELF64 file of type `ET_EXEC` for `EM_AARCH64`, in the little-endian formats of the System V Application Binary Interface and of *ELF for the Arm 64-bit Architecture (AArch64)*. Its one `PT_LOAD` segment maps the whole file at the address `0x400000`, to be read and run, aligned to 64 KiB. The code starts at offset `0x1000` in the file, and the entry is at `0x401000` plus its offset in the code. The file has no section table, interpreter, dynamic section or signature. The writer gives an empty string if the entry is not a multiple of 4 within the code.

## Efficiency

The compiler reads its input by position with `char` and `length`, never as the list of all its characters, and it computes with `+`, `-`, `*`, `<`, `ash` and `binary-logxor`, never with `floor`, `mod`, `expt`, `logand` or `logior`, which the reference runner runs by their definitions.

Its tables, of names in `index.lisp` and `data.lisp` and of labels in `a64.lisp`, are binary trees branching on the bits of a hash, 12 bits for names and 16 for labels, whose leaves are AVL trees, binary search trees in which the heights of the two children of a node differ by at most one. A lookup takes at most as many steps as the hash has bits, then a number of comparisons of keys that grows as the logarithm of the number of keys with that hash, whatever the names. The formals in scope in a function are held in an AVL tree too.

The data builder and the assembler write each run of fields into a string of at most 512 bytes, and keep each large string constant as a string of its own. The Mach-O writer hashes each whole page within one of these strings by position, and gathers a page that spans two into a string of 4,096 bytes. `image-string` (`a64.lisp`) joins the strings into the executable: it reads each by position from its end, the last first, makes one cons for each byte, and makes the string once.

## Tests

Each test compares the compiler with the reference runner, the system's tools, or a fixed expectation, and prints what it found. All need `build/runner/boymoo-run`. `test-front.sh`, `test-targets.sh`, and `test-symbols.sh` given the compiled compiler, use `build/compiler/compiler-2`, which `sh compiler/bootstrap.sh` makes; `test-numbers.sh`, and `test-front.sh` with `--reference`, compile with `compile.sh`, which needs what `sh compiler/build.sh` writes; `test-a64.sh`, `test-symbols.sh` with no argument and `test-checker.sh` build what they need.

- `sh compiler/test-front.sh` runs the reference runner and the compiled compiler on each case of "What the compiler accepts", runs the executable when one is made, and compares the statuses and values; with `--reference` it compiles with `compile.sh` instead.
- `sh compiler/test-a64.sh` certifies and exports the assembler alone, and compares the bytes of its test items with those of the system assembler, `clang -arch arm64 -c`, read with `otool`.
- `sh compiler/test-numbers.sh` compiles one program that computes every numeric primitive and the jets on a fixed set of operands, among them the bounds of the immediate integers, 2<sup>64</sup>, 2<sup>128</sup>, fractions, complex rationals and data that are not numbers, with a collection in the midst of the arithmetic, and compares the text of its results with the reference runner's.
- `sh compiler/test-symbols.sh build/compiler/compiler-2` compiles `test-symbols.txt`, which interns 4,000 names, two with the same hash, and interns each again, and asks about imports, witnesses and hidden packages, and compares the results with the reference runner's; with no argument it compiles with `compile.sh`.
- `sh compiler/test-targets.sh` compiles a program that gives back its input, for macOS and for Linux, checks the headers of both files with `od` and `awk` and the signature with `codesign -v --strict`, and runs the macOS executable. When `docker` reaches a running Colima, it also makes a local image that holds only the Linux executable, with `docker import` from a `tar` archive, runs it with no network and a root that cannot be written, and removes the image; otherwise it says so and skips that run.
- `sh compiler/test-checker.sh` is described under "The compiled checker", below.

Run on 2026-11-25, each test passed. `test-front.sh` found the runner and the compiler agreeing on every case: the runner rejected each of the 22 texts not in the format with status 2, and the compiler stopped on each with status 1 and wrote no executable; on the others both gave the same value, or, for the entry with no definition, the same stop. `test-a64.sh` printed `A64 assembler agrees with the system assembler on 284 bytes.`; `test-numbers.sh` printed `Numeric primitives and jets agree on 16281 bytes of results.`; `test-symbols.sh build/compiler/compiler-2` found the two programs agreeing on all five of its comparisons. `test-targets.sh` checked the seven load commands of a Mach-O file of 214,784 bytes with its entry at offset `0x1090`, and an ELF file of 205,484 bytes with its entry at `0x40106c`; `codesign` accepted the signature, and the macOS executable, and the Linux one in Colima, gave back their input and exited with status 0.

## The compiled checker

`checker-entry.lisp` defines the entry of the checker of `PLAN.md`, step 4, as an executable. Its standard input holds five strings, each after its length in bytes as four bytes, the most significant first: the ground theory, the library, the statements, the proofs and the library's proofs. It gives them to `BOYMOO::CHECK-FOUR` and writes the verdict and a line feed, or `invalid checker input frame` and a line feed if the input is not five such strings.

```
sh compiler/build-checker.sh
sh compiler/check.sh LIBRARY STATEMENTS PROOFS [LIBRARY-PROOFS]
```

`build-checker.sh` has `checker/build.sh` build the checker, has ACL2 certify the entry beside the checker's books and the exporter export it, writes the compiler's input, `build/compiler/checker-test/checker.input`, and compiles it on the reference runner to `build/compiler/checker`. `check.sh` takes the arguments of `checker/check.sh`, gives the compiled checker `spec/ground.txt` and the four files as its five strings, and writes the verdict line; unlike `checker/check.sh`, it writes no second line saying what failed in a rejection.

The library check of `PLAN.md`, step 6, with the library as the first input, the second and third empty, and the library's proofs as the fourth, run on 2026-11-26 on Apple silicon, each under `/usr/bin/time -l`, after `sh compiler/build-checker.sh` and `: > build/empty`:

| Command | Verdict | Elapsed | Most bytes resident |
|---|---|---:|---:|
| `sh compiler/check.sh build/export/library.statements build/empty build/empty build/prover/library.proofs`, twice | `accepted` | 24.14 s, 23.20 s | 352,288,768 |
| the same with `env RUNNER=build/runner-fast/boymoo-run-fast sh checker/check.sh` | `accepted` | 27.12 s | 580,386,816 |
| the same with `sh checker/check.sh`, on the reference runner | `accepted` | 114.17 s | 609,173,504 |

The input was 164,776,812 bytes, of which `build/prover/library.proofs` is 161,628,902. The times of `checker/check.sh` include writing the inputs as quoted strings for the runner.

`sh compiler/test-checker.sh [N]` builds the compiled checker with `build-checker.sh`, and runs it, and the checker on the reference runner, on `spec/example` and on every case of `checker/cases/` and `checker-js/cases/` whose verdict is recorded, comparing the verdicts with each other and with the record. Then it runs the compiled checker on each book of `export/books.txt` that has been exported, with proofs that skip every obligation, as `checker/books.sh` does, and the reference runner on the first `N` of them, 20 if `N` is not given. It writes each result to `build/compiler/checker-test/results.tsv`, and the books with no export to `build/compiler/checker-test/missing-books.txt`. It exits with status 1 if a book has no export, if the compiled checker stops on an input, or if, on an input with a reference run, the compiled checker's verdict, the reference runner's and the recorded one are not all the same. It needs `acl2`, `timeout` and `zsh`, whose `time` measures each run, and runs on macOS.

Run on 2026-11-26 as `sh compiler/test-checker.sh 460`, it printed `Inputs run: 1233. Compiled checker matched 1233 expected verdicts and agreed with the reference runner on 1233. Compiled checker stops: 0.`: on `spec/example`, the 772 cases with recorded verdicts and all 460 books, the compiled checker and the checker on the reference runner gave the same verdict, and the recorded one where there is one. The compiled checker took 243.45 s of elapsed time in all, with at most 530,366,464 bytes resident, and the reference runner 1,031.20 s, with at most 526,712,832 bytes. Each run is stopped after 15 s; none was.
