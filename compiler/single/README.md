# The single-pass compiler

The single-pass compiler: a program in ACL2 Core that turns ACL2 Core program text into an executable for aarch64, for macOS or for Linux, turning each definition straight into assembly items. It shares with the many-pass compiler of `compiler/` the reader, the index, the data builder, the assembler and the writers of executables, and its executables have the same input, output, exit statuses, data representation and static block as those of the many-pass compiler. `compiler/README.md` describes what the two share: the input and the executable, what the compilers accept, the data, the runtime's routines and their contracts, numbers, the system, the assembly language, the executable files, the tests and the compiled checker and prover. This document describes only what is particular to the single-pass compiler.

The reference runner runs the compiler once, to compile it; the compiled compiler, compiling its own input, gives its own bytes again. The compiled compiler is the reference with which the many-pass compiler's executables are compared (`compiler/README.md`, "Results").

Paths below are given from the root of the repository, from which every command is run.

## The parts

| File | What it is |
|---|---|
| `gen.lisp` | The code generator: it turns each definition into assembly items. |
| `runtime.lisp` | The runtime of this compiler, as assembly items: memory and its collector, the primitives, the functions of the prelude, and reading and writing. |
| `compile.lisp` | `COMPILE-TEXT`, which joins the parts. |
| `build.sh` | Has ACL2 certify the compiler's books and the exporter export them. |
| `compile.sh` | Compiles an input on the reference runner, with the decoder of `compiler/decode.sh`. |
| `bootstrap.sh` | Builds the compiler, has the reference runner compile it, has the result compile it again, and compares the two. |
| `proofs/` | ACL2 books that prove parts of the theorem that this compiler preserves the meaning of a program, with `certify.sh`, which certifies them (`compiler/single/proofs/README.md`). |

The other books of the compiler are in `compiler/`, shared with the many-pass compiler: `package.lsp`, `read.lisp`, `index.lisp`, `data.lisp`, `a64.lisp`, `macos.lisp`, `sha256.lisp` and `linux.lisp` (`compiler/README.md`, "The parts").

## Building and running

```
sh compiler/single/build.sh
```

has ACL2 certify the compiler's books in `build/compiler/single/acl2/`, those of `compiler/` and its own, and the exporter write the compiler's statements and program text as `build/compiler/single/compiler.statements` and `build/compiler/single/compiler.program`. Beside them it writes `ground.program`, the definitions of the ground theory, and `library.statements`, the lines of ACL2's library that the compiler calls, chosen by `checker/library.awk`. From those lines it leaves out the definitions of `ACL2::HARD-ERROR` and `ACL2::THROW-NONEXEC-ERROR`: ACL2 defines each to return `NIL`, but runs each as an error that ends the computation. With no definition, a call of either stops, as in ACL2; with its definition, it would return `NIL`, and the compiler would go on as if there were no error. The script needs `acl2`, `build/runner/boymoo-run` and `build/export/library.statements`. With `--a64` it certifies and exports the assembler, `compiler/a64.lisp`, alone, and writes its files into `build/compiler/a64`, for `compiler/test-a64.sh`.

```
sh compiler/single/bootstrap.sh
```

builds the compiler, writes its input, `build/compiler/single/compiler.input`, and has the reference runner compile it to `build/compiler/single/compiler-1`, a macOS executable, which compiles the same input to `build/compiler/single/compiler-2`. It prints the time of each and compares the two byte for byte. Run on 2026-11-25 on Apple silicon, the reference runner took 20.62 s (19.577 s of processor time, with a peak of 28,720 KB of memory held), and `compiler-1` took 0.43 s; the two executables were identical, of 974,336 bytes. `/usr/bin/time -l build/compiler/single/compiler-2 < build/compiler/single/compiler.input > /dev/null`, run three times on the same day, took from 0.40 s to 0.43 s, with at most 20,365,312 bytes resident.

```
sh compiler/single/compile.sh [-v] INPUT > EXECUTABLE
build/compiler/single/compiler-2 < INPUT > EXECUTABLE
```

compile an input on the reference runner, with its prelude, and with the compiled compiler; with `-v` the runner also prints its time and peak of memory. `chmod +x EXECUTABLE` makes the result executable.

## The calling convention

The registers that the runtime sets up and uses, the value stack and the collector's roots, and the contracts of the runtime's routines, are in `compiler/README.md`, "The runtime". A function that this compiler writes keeps `x19` to `x22` and `x29`, as the routines of the runtime that return do, besides `x23` to `x28` and `sp`; `x0` to `x17` and `NZCV` are free across calls, and a compiled call returns its datum in `x0`.

**The value stack** holds the arguments and the live data of every call in progress. A compiled function of `n` arguments finds them in the `n` words below `x25`, may push words above them, and returns with `x25` lowered by `8n`. A call in the last position of a body moves its arguments to the place of the caller's own, restores the machine frame and jumps, so that a recursion in the last position takes no room on either stack. The prologue calls `rt:deep` if its frame of 16 bytes on the machine stack would go below `x23`, and `rt:grow` if its frame on the value stack would pass `x24`.

The generator computes `CAR`, `CDR` and `CONSP` in the function's own code, always; `IF` as a comparison of its test with `NIL`, the datum 34; `EQUAL` where the two words are the same or one is an immediate integer or a character; and `BINARY-+`, `UNARY--` and `<` of two immediate integers whose result is one. Every other call of a primitive is a call of its routine, `prim:NAME`, where `NAME` is the primitive's symbol as written; a call of one of the five functions of the prelude listed in `index.lisp`, chosen by name, is a call of `jet:NAME`, whatever the program text says of the function, as with the reference runner's `-j`.

**The program's entry** is the label `rt:entry`, which the compiler gives to the definition of the entry function; when that function has an attachment, is computed by the runtime, or has no definition, the compiler makes a definition that calls it, and gives the label to that. `rt:start` calls `rt:entry` as a compiled function.

## Its runtime's memory

Each of the two spaces of the copying collector of `runtime.lisp` reserves 4 GiB of addresses by default, or the size specified by `heap-limit`. Objects with a header grow from one end of the active space and conses from the other. They share a budget that a collection sets to the largest of 64 KiB, twice the bytes that survived, and the bytes that survived together with the pending request, up to the size of the space. An allocation that exceeds the available bytes after collection stops with status 3. A collection gives back to the system the pages it used at both ends of the space it leaves, rounded out to 64 KiB. Standard input is read into a mapping of its own, and every string of 256 KiB or more is allocated in one; such strings keep their addresses, and a collection marks those it reaches, unmaps the rest, and sets a budget for further mappings. The value stack reserves 1 GiB of addresses, and the machine stack is a mapping of 64 MiB.

## Between the parts

`COMPILE-TEXT` takes the input as a string and gives the executable as a string:

1. `READ-PROGRAM` reads the input into its lines.
2. `INDEX-LINES` finds the last definition and the last attachment of each name, the package lines, the entry and the target; `RESOLVE-ATTACHMENTS` follows the chains of attachments and rejects a cycle.
3. `DATA-BUILD` lays out the static block, and gives the table from the text of each constant to its datum. `COMPILE-ENTRY-DEFINITIONS` makes a definition for the entry when the entry's function has an attachment, is a routine of the runtime, or has no definition.
4. `COMPILE-ITEMS` puts together the system's routines, `(SYSTEM-CODE)` or `(LINUX-SYSTEM-CODE)`, the runtime's, `(RUNTIME-CODE)`, the compiled functions, which `GEN-FUNCTIONS` writes from the definitions, the arities, the attachments and the table of constants, and last the static block at the label `data:static`.
5. `A64-ASSEMBLE-IMAGE` assembles them, and gives the image and the offset of `os:main` in it.
6. `MACHO-IMAGE-EXECUTABLE` or `ELF-IMAGE-EXECUTABLE` writes the executable from the image and that offset. `MACHO-EXECUTABLE` and `ELF-EXECUTABLE` do the same from the bytes as one string.

## Efficiency

The compiler reads its input by position with `char` and `length`, never as the list of all its characters, and it computes with `+`, `-`, `*`, `<`, `ash` and `binary-logxor`, never with `floor`, `mod`, `expt`, `logand` or `logior`, which the reference runner runs by their definitions.

Its tables, of names in `compiler/index.lisp` and `compiler/data.lisp` and of labels in `compiler/a64.lisp`, are binary trees branching on the bits of a hash, 12 bits for names and 16 for labels, whose leaves are AVL trees, binary search trees in which the heights of the two children of a node differ by at most one. A lookup takes at most as many steps as the hash has bits, then a number of comparisons of keys that grows as the logarithm of the number of keys with that hash, whatever the names. The formals in scope in a function are held in an AVL tree too.

The data builder and the assembler write each run of fields into a string of at most 512 bytes, and keep each large string constant as a string of its own. The Mach-O writer hashes each whole page within one of these strings by position, and gathers a page that spans two into a string of 4,096 bytes. `image-string` (`compiler/a64.lisp`) joins the strings into the executable: it reads each by position from its end, the last first, makes one cons for each byte, and makes the string once.

## Test results

Run on 2026-11-26, and again on 2026-11-27 with the same results, with this compiler, each of the tests of `compiler/README.md`, "Tests", passed. `sh compiler/test-front.sh build/compiler/single/compiler-2` found the runner and the compiler agreeing on every case: the runner rejected each of the 24 texts not in the format with status 2, and the compiler stopped on each with status 1 and wrote no executable; on the others both gave the same value, or, for the entry with no definition, the same stop. `sh compiler/test-numbers.sh` printed `Numeric primitives and jets agree on 16281 bytes of results.`; `sh compiler/test-symbols.sh build/compiler/single/compiler-2` found the two programs agreeing on all five of its comparisons. `sh compiler/test-targets.sh build/compiler/single/compiler-2` checked the seven load commands of a Mach-O file of 214,784 bytes with its entry at offset `0x1090`, and an ELF file of 205,504 bytes with its entry at `0x40106c`; `codesign` accepted the signature, and the macOS executable, and the Linux one in Colima, gave back their input and exited with status 0.

On 2026-11-27, `sh compiler/single/bootstrap.sh` had the reference runner compile the
compiler in 20.68 s and the result compile the same input in 0.63 s, and printed
`The two compiler executables are byte-for-byte identical.`; each is 974,336 bytes.
On 2026-11-26 it printed the same line. The following
test, run on the same date, makes 100,000 live conses. At 1 MiB it printed
`memory exhausted: the heap is at its largest` on standard error and
exited with status 3. At 2 MiB it printed `ok` and exited with status 0.

```sh
cat > build/compiler/single/heap-limit.input <<'EOF'
(package "COMMON-LISP" COMMON-LISP::NIL)
(package "ACL2" COMMON-LISP::NIL)
(define COMMON-LISP::NIL (ACL2::BUILD-LIST (ACL2::N ACL2::XS) (COMMON-LISP::IF (COMMON-LISP::< ACL2::N (COMMON-LISP::QUOTE 1)) ACL2::XS (ACL2::BUILD-LIST (ACL2::BINARY-+ ACL2::N (COMMON-LISP::QUOTE -1)) (COMMON-LISP::CONS ACL2::N ACL2::XS)))))
(define COMMON-LISP::NIL (ACL2::MAIN (ACL2::TEXT) (COMMON-LISP::IF (COMMON-LISP::CONSP (ACL2::BUILD-LIST (COMMON-LISP::QUOTE 100000) (COMMON-LISP::QUOTE COMMON-LISP::NIL))) ACL2::TEXT (COMMON-LISP::QUOTE ""))))
(entry ACL2::MAIN)
EOF
for limit in 1 2; do
    { cat build/compiler/single/heap-limit.input; printf '(heap-limit %s)\n' "$limit"; } |
        build/compiler/single/compiler-2 > build/compiler/single/heap-limit-sample
    chmod +x build/compiler/single/heap-limit-sample
    printf 'ok\n' | build/compiler/single/heap-limit-sample
    printf '%s MiB executable exit %s\n' "$limit" "$?"
done
```

## The compiled checker

The compiled checker and its commands are described in `compiler/README.md`, "The compiled checker". With `COMPILER=build/compiler/single/compiler-2`, this compiler writes it.

The library check of `PLAN.md`, step 6, with the library as the first input, the second and third empty, and the library's proofs as the fourth, run on 2026-11-26 on Apple silicon, each under `/usr/bin/time -l`, after `sh compiler/build-checker.sh`, with `COMPILER` unset, so that this compiler wrote the checker, and `: > build/empty`:

| Command | Verdict | Elapsed | Most bytes resident |
|---|---|---:|---:|
| `sh compiler/check.sh build/export/library.statements build/empty build/empty build/prover/library.proofs`, twice | `accepted` | 24.14 s, 23.20 s | 352,288,768 |
| the same with `env RUNNER=build/runner-fast/boymoo-run-fast sh checker/check.sh` | `accepted` | 27.12 s | 580,386,816 |
| the same with `sh checker/check.sh`, on the reference runner | `accepted` | 114.17 s | 609,173,504 |

The input was 164,776,812 bytes, of which `build/prover/library.proofs` is 161,628,902. The times of `checker/check.sh` include writing the inputs as quoted strings for the runner.

Run on 2026-11-26 as `sh compiler/test-checker.sh 460`, with `COMPILER` unset, it printed `Inputs run: 1233. Compiled checker matched 1233 expected verdicts and agreed with the reference runner on 1233. Compiled checker stops: 0.`: on `spec/example`, the 772 cases with recorded verdicts and all 460 books, the compiled checker and the checker on the reference runner gave the same verdict, and the recorded one where there is one. The compiled checker took 253.54 s of elapsed time in all, with at most 530,366,464 bytes resident, and the reference runner 1,052.28 s, with at most 516,472,832 bytes. Each run is stopped after 15 s; none was.
