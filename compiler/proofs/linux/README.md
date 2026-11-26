# Linux loading, process entry and composition

The books in this directory are work package P4 of the proof of the
compiler, described in `compiler/proofs/README.md`. They concern the
Linux target: the ELF file that the compiler writes, the loader model
`proof-load-linux` of `compiler/proofs/foundations/loading.lisp`, and the
first part of `compile-text`, up to the world in which the compiled
program starts.

All the books are in logic mode. None uses `defaxiom`, `skip-proofs` or
any other way of admitting a theorem without proof, and none includes a
book from outside the repository.

## The books

| Book | Includes | Subject |
| --- | --- | --- |
| `arithmetic.lisp` | nothing | `floor`, `ceiling`, `mod`, `ash` and `logand` on natural numbers |
| `elf.lisp` | `interfaces`, `arithmetic` | the file written by `elf-image-executable` |
| `load.lisp` | `elf` | the world built by `proof-load-linux` |
| `install.lisp` | `load` | the bytes that `proof-load-linux` leaves in memory |
| `compose.lisp` | `install` | `compile-text` for the Linux target, and the start of the program |
| `wrappers.lisp` | `load` | the system call wrappers of `linux-system-code` up to their SVC |

## What the books prove

The names below are the names of the theorems in the books. The
hypothesis `(linux-elf-arguments-p image entry)` says that `image` is a
well-formed image in the sense of `proof-image-p` (a size followed by
string fragments whose lengths add up to the size), that `entry` is a
natural number divisible by four with `entry + 4` at most the image
size, and that the load address of the code plus the image size is at
most 2^63.

### Arithmetic (`arithmetic.lisp`)

- `linux-floor-bounds`: for a nonnegative rational `x`, `(floor x 1)` is
  a natural number with `(floor x 1) <= x < (floor x 1) + 1`. It is
  proved from the definitions of `floor` and `nonnegative-integer-quotient`
  in the ACL2 ground theory.
- `linux-logand-mask`: for natural numbers `n` and `x` with `x < 2^n`,
  `(logand x (- (expt 2 n) 1))` equals `x`. This is what makes the model's
  `a64-unsigned` the identity on values in range.
- `linux-round-up-covers`: for a natural `e` and positive integer `c`,
  `e <= c * (ceiling e c)`, so rounding an address up to a page boundary
  never lowers it.
- `linux-word-aligned-test` and `linux-mod-4-of-sum` connect the
  compiler's alignment test `(equal entry (ash (ash entry -2) 2))` with
  `(equal (mod entry 4) 0)`, and show that adding a multiple of four
  keeps a multiple of four.

### The ELF file (`elf.lisp`)

- `linux-image-string-characters`: `image-string` of a list of string
  fragments is the string of their characters in order.
- `linux-elf-image-executable-characters`: the characters of the file
  that `elf-image-executable` writes are the header produced by
  `elf-prepend-header` followed by the characters of the image fragments.
- `linux-elf-image-executable-length`: the file is 4096 bytes longer than
  the image.
- `linux-elf-image-executable-code`: from offset 4096 on, the file holds
  exactly the characters of the image fragments.
- `linux-elf-image-executable-entry`: the entry field of the file is the
  code address `#x401000` plus the entry offset.
- `linux-elf-image-executable-accepted`: under
  `linux-elf-arguments-p`, the file is accepted by `proof-elf-p`, the
  loader's recognizer of a single read and execute segment with an
  aligned entry inside the code.
- `linux-entry-check-example`: a five-byte image with its entry at
  offset 4. The writer, like `proof-elf-p`, asks for a whole instruction
  at the entry, so for this image it writes the empty string. In
  `linux-system-code` the label `os:main` is followed by three
  instructions, so the hypothesis `entry + 4` at most the image size is
  expected of every compiled program; it is not proved here, and is part
  of the obligation that `compose.lisp` carries as
  `linux-text-obligations-p`.

The field lemmas behind these theorems read each little-endian field
back from the characters that `elf-prepend-le` writes
(`linux-le-list-of-prepend-le`) and skip the fields before it
(`linux-prepend-le-nthcdr`, `linux-prepend-zeroes-nthcdr`).

### The loader (`load.lisp`)

For any file, machine and environment on which `proof-load-linux`
succeeds:

- `linux-load-pc`: the program counter of the loaded machine is the
  entry field of the file.
- `linux-load-regions`: the regions are the given regions with one more
  in front, from `#x400000` to the end of the file rounded up to the page
  size, with mode `:rx`.
- `linux-load-streams`: the page size is the one given, the input stream
  is the bytes of the input string, both output streams are empty, the
  replies are the ones given, and the process has not stopped.
- `linux-load-registers`: the general registers, the stack pointer and
  the condition flags are those of the machine given.
- `linux-load-code-executable`: the part of the file after its first
  4096 bytes, at address `#x401000`, is covered for execution.

For a file written by `elf-image-executable`, with
`linux-load-environment-p` stating the loader's conditions on the
input, page size, regions and stack pointer:

- `linux-load-executable-accepted`: `proof-load-linux` succeeds.
- `linux-load-executable-pc`: the program counter is `#x401000` plus the
  entry offset.
- `linux-load-executable-code-executable`: the whole image, at
  `#x401000`, is covered for execution.

### The loaded bytes (`install.lisp`)

- `linux-load-byte`: after a successful load, the byte that the model's
  `a64-load` reads at any address from `#x400000` to the end of the file
  is the character code of the file at that offset.
- `linux-load-characters`: a run of bytes read with `proof-byte-list`
  inside the file gives the matching characters of the file.
- `linux-load-fragments`: string fragments whose characters appear in
  the file at some offset are found by `proof-fragments-at-p` at the
  matching address.
- `linux-load-executable-image`: for a file written by
  `elf-image-executable`, the loaded machine meets `proof-image-at-p` for
  the image at `#x401000`. Together with
  `linux-load-executable-code-executable` and `linux-load-executable-pc`,
  this says that the loader installs the exact fragments of the image,
  with execute permission, and starts at the entry.

### Composition (`compose.lisp`)

`linux-text-items` follows `compile-text` up to the list of items that it
assembles, and returns whether the program has an entry line, whether
its target is Linux, and the items. `linux-text-image` and
`linux-text-entry` are the image and the offset of `os:main` that
`a64-assemble-image` gives for those items.

- `linux-compile-text-is-elf`: when the program has an entry line and
  the Linux target, `compile-text` is `elf-image-executable` of that image
  and that offset.

The predicate `(linux-text-obligations-p text machine regions page
input)` collects what the other work packages and the environment must
supply: the entry line, the Linux target, `linux-elf-arguments-p` for the
assembled image and the offset of `os:main`, and
`linux-load-environment-p`. Under it:

- `linux-compiled-start-accepted`: `proof-compiled-start` gives a world.
- `linux-compiled-start-pc`: its program counter is `#x401000` plus the
  offset of `os:main`.
- `linux-compiled-start-linked`: the world meets `proof-linked-image-p`
  for the compiled items, the entry `"os:main"` and the base `#x401000`,
  which is the linked-image contract of the shared books.
- `linux-compiled-start-streams`: the world has the input as its input
  stream, empty output streams, the given replies, no stop, and the
  registers and stack pointer of the machine given.

### System call wrappers (`wrappers.lisp`)

The instructions below are given in the form that the model's decoder
returns. `linux-exit-instructions-are-assembled` and
`linux-movz-8-is-assembled` show, by evaluation, that they are the
decoded words that the assembler's `a64-word` encodes for the items
`(:movz 8 NUMBER 0)` and `(:svc 0)` of `linux-system-code`.

- `linux-sys-exit-wrapper`: in a world that has not stopped, with the
  two instructions of `sys:exit` at the program counter, two steps under
  the kernel rules stop the process with exit status the low eight bits
  of register 0.
- `linux-svc-wrapper`: for a system call number below 2^16, with
  `(:movz 8 NUMBER 0)` at the program counter and `(:svc 0)` after it,
  two steps give exactly the world that the kernel rule `proof-linux-svc`
  gives for that number, applied to the world after the move. With
  `linux-after-movz-registers`, which says that the move changes no
  register other than register 8, this says that `sys:map`,
  `sys:release`, `sys:unmap`, `sys:read` and `sys:write` reach the Linux
  SVC with numbers 222, 233, 215, 63 and 64 and with the arguments that
  were in registers 0 to 5.

Both theorems ask for the world to be a cons, which every world built by
`proof-world` is.

## What the books do not prove yet

These parts of P4 remain open goals.

- The rest of the system call wrappers: the moves before the SVC in
  `sys:map` and `sys:release`, the `ret` after it, and the result of each
  wrapper under the kernel rules, in particular the `cmp` and `csel` that
  turn a failed mapping into zero in `sys:map`. The step after a `ret`
  needs the fact that `a64-unsigned` of 64 bits is idempotent for every
  integer, which `linux-logand-mask` gives only for natural numbers
  below 2^64.
- `os:main`: the call of `rt:start`, and the exit with status 1 if it
  returns.
- `rt:start`: the initial mappings, the copy of the static data, the
  input loop with its end of file and maximum-size checks, and the call
  of `rt:entry` with its input slot.
- `rt:write-all` on short writes, and the exit and diagnostic paths of
  `runtime-stop-code`, including the exit status when a diagnostic write
  fails.
- The conditional whole theorem. The books carry the start of the
  program as far as `proof-linked-image-p`, with the program counter at
  `os:main`. The obligations that discharge `linux-elf-arguments-p` for a
  compiled program (an assembled image of the right form, with `os:main`
  word aligned and followed by an instruction, and a size below 2^63)
  belong to the assembly work package and are carried here as the
  hypothesis `linux-text-obligations-p`.

## Certification

Run from the root of the repository, after the shared books have been
certified with `sh compiler/proofs/certify.sh --foundations`:

```
sh compiler/proofs/linux/certify.sh
```

It certifies the books in the order `arithmetic`, `elf`, `load`,
`install`, `compose`, `wrappers`, with ACL2 8.7 found as `acl2` on the
`PATH`, and prints one line `Certified compiler/proofs/linux/BOOK.lisp.`
for each book. On 26 November 2026 it printed that line for all six
books and exited with status 0, in 12 seconds of elapsed time.
