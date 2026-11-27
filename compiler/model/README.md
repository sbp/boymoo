# The models

Two models in ACL2, the start of a proof that the compiler of `compiler/README.md` preserves the meaning of the programs it compiles: one of what an ACL2 Core program computes, and one of the A64 machine that runs the code the compiler writes. Paths below are given from the root of the repository, from which every command is run.

## The model of ACL2 Core programs

The ACL2 book `core.lisp` defines the meaning of translated terms in
`spec/language.md`, sections 3 to 5, with the prelude of
`runner/README.md` in force. Load `package.lsp` before including the book.
The entry points below belong to the package `BOYMOO-MODEL`.

- `(core-program definitions attachments visible-packages hidden-witnesses)`
  makes a program. Each definition is `(name formals body)` and each
  attachment is `(name target)`. Put later lines first in each list so
  that the first matching entry is in force. The bodies are translated
  terms and the ruler-extenders are discarded. Supply the ground and
  library definitions that the program uses in the definition list.
- `(core-eval term env program fuel)` evaluates a term. The environment
  pairs variables with their values as dotted pairs. Supply an empty
  environment for a closed term. `core-eval-args` evaluates a list of
  terms from left to right. `(core-call name args program fuel)` applies
  a named function to a list of values.
- A result is `(:value . datum)`, `:no-value` or `:out-of-fuel`.
  `core-value-p` recognizes a value and `core-datum` gets its datum.
  The fuel bounds evaluator depth. Each recursive evaluator invocation
  receives one less than its caller, including an invocation that
  follows an attachment. A function or lambda body starts with the
  bindings of its formals. Only the selected branch of an `if` and
  the logical half of an `mbe` are evaluated.

The model uses ACL2's primitives with their logical completions. For
package operations the ACL2 session must contain the program's packages
with the same imports. The program lists the names of its additional
visible packages and the `ACL2-PKG-WITNESS` symbols of its hidden
packages. The ground package names are built in. Visibility determines
whether `pkg-imports` and `pkg-witness` compute a value on a string.
Interning the witness name in a symbol's package lets the model recognize
hidden symbols before calling `symbol-package-name`. Interning itself
works in hidden packages.

The prelude uses ACL2's values of `ash`, `binary-logxor`, `length`,
`char` and `subseq`. Definitions for these names are ignored.
`ash` gives zero immediately when its first argument fixes to zero.
The `subseq` implementation can finish dropping elements when it
reaches an atom. These cases give the logical values described in
`EDGE-CASES.md`, entries 2.10 and 2.11.

The input is assumed to be well-formed program and term data. Reading
text, checking scope and arities, and rejecting attachment cycles are
the reader and compiler's work. Fuel represents the limit of the
recursive definition. The model omits platform stack and memory limits
because their effects depend on the implementation of a runner.
The book states equations about evaluation. The relation to compiled
instructions and the host's representation of data is a separate proof.

ACL2 certifies the following results in logic mode.

- `core-eval-more-fuel` and `core-call-more-fuel` say that increasing
  natural-number fuel preserves an evaluation result other than
  `:out-of-fuel`. `core-eval-step-more-fuel` supplies the corresponding
  result for the interpreter's three cases, including argument lists.
- `core-call-of-prelude` and `core-prelude-values` give ACL2's value
  for a prelude application with positive fuel and no attachment on
  its name. `core-ash-is-ash` and `core-subseq-is-subseq` equate the
  model's two helpers with the corresponding ACL2 functions.
- `core-defined-call-result` gives a call's result directly as the
  evaluation of its definition body. `core-tail-call-result` gives
  the result of an ordinary call term directly as the callee's result
  once the arguments have values. Together they describe a call in
  the last position without a transformation of the callee's result.

Run this command from the repository root.

```sh
sh compiler/model/core-test.sh
```

The command certifies the book and compares values and stops line for
line with `build/runner/boymoo-run -j`. The test passes small program
text fixtures to the reference runner and reads the same definition
and attachment lines as ACL2 data. It sets guard checking to `:none`
and uses the repository's canonical printer. The test declares the
package used in the hidden-package cases in ACL2 so that its data can
be read, and marks it hidden in the model and runner inputs.
On 2026-11-26, ACL2 8.7
certified the book, 13 values and four no-value stops agreed, and the
fuel check distinguished exhaustion from a value of `NIL`. The
certificate, ACL2 log and comparison files are under `build/compiler/core/`.

## The model of A64

The ACL2 books `a64-state.lisp`, `a64-decode.lisp` and `a64.lisp`
describe the machine used by the calling convention and code image in
`compiler/README.md`. Load `compiler/model/package.lsp` before including
`a64.lisp`. The entry points belong to `BOYMOO-MODEL`.

- `(a64-state registers sp pc nzcv memory)` constructs a machine.
  The register list maps the numbers 0 through 30 to unsigned
  64-bit values. The memory list maps 64-bit addresses to bytes.
  Both lists hold dotted pairs and use zero for an absent entry.
  The flags occupy four bits, with N in bit 3 and V in bit 0.
- `a64-read-reg` and `a64-write-reg` take a register number, a width
  and an argument that selects SP when the number is 31. With that
  argument false, register 31 reads as zero and discards writes.
  A write of width 32 clears the upper 32 bits. `a64-load` and
  `a64-store` take a byte count and address. They transfer little-endian
  values with each address reduced modulo 2^64.
- `(a64-decode word)` gives a list whose first element identifies the
  instruction class and whose other elements give its operands, or
  gives `:undefined`. Aliases use the same encodings and execution
  functions as their underlying instructions.
- `(a64-step machine)` fetches the four bytes at PC, decodes the
  instruction and gives the resulting machine, `:undefined`, or
  `(:svc immediate x16 x8)`, with the register values at the system
  call. A branch with link records the next sequential PC in X30.
- `(a64-run steps start end return-pc machine)` gives two values,
  a stop reason and the last machine. It checks for `:return` at
  `return-pc`, then for `:outside` when the PC is outside the
  half-open interval from `start` to `end`, then for `:limit` when
  the step budget is used up. Use `nil` as the return address to
  omit that stop. The region check requires both bounds. If an
  instruction gives `:undefined`, the run returns that reason and
  the machine at the failed step. For SVC it returns the event and
  the machine with PC still at SVC. The event supplies X16 for
  Darwin and X8 for Linux, so the caller can apply the appropriate
  system call convention.

The instructions in the table below are those of the assembler's
items in “The assembly language” of `compiler/README.md`, but for
`:ldur`, `:stur`, `:ldurb`, `:tbz` and `:tbnz`, which only the
many-pass compiler writes: the model does not decode LDUR, STUR, LDURB,
TBZ and TBNZ, which therefore fall outside its scope. Labels
locate bytes, and `:bytes`, `:quad` and `:image` supply data. The
reference is the *Arm Architecture
Reference Manual for A-profile architecture* (ARM DDI 0487),
sections “A64 Instruction Set Encoding,” “A64 Base Instruction
Descriptions” and “Shared Pseudocode.”

| Instructions | Encodings covered |
|---|---|
| MOVZ, MOVK and MOVN | Move-wide immediate. |
| ORR, AND, EOR and ANDS | Shifted register, including MOV, TST and the MVN alias of ORN. |
| ADD, SUB, ADDS and SUBS | Immediate and shifted register, including CMP, CMN and NEG, and the immediate MOV to or from SP. |
| AND, ANDS and ORR | Bitmask immediate, including TST. |
| UBFM and SBFM | Bitfield, including LSL, LSR, ASR, UBFX and SBFX. |
| LSLV, LSRV and ASRV | Variable register shifts. |
| CLZ of X | The number of leading zero bits, from 0 to 64. |
| MUL, SMULH, MSUB, SDIV and UDIV | 64-bit multiply and divide. Division by zero gives zero, and signed division truncates toward zero. |
| CSEL and CSINC | Conditional select, including CSET. |
| CCMP of X | Conditional compare of two registers, which the assembler writes as the second word of a flag-setting immediate instruction whose source is register 31. |
| LDR and STR of W or X, LDRB and STRB | Unsigned scaled offset, signed pre-index and post-index, and register offset with optional scaling. |
| LDP and STP of X | Signed scaled offset, pre-index and post-index. |
| ADR and ADRP | PC-relative byte and page addresses. The assembler writes ADRP followed by ADD for `:adr-far`. |
| B, BL, B.cond, CBZ, CBNZ, BR, BLR and RET | Immediate and register branches. |
| SVC | Stops with the immediate and the system call register values. |

The model treats reserved encodings and constrained-unpredictable
register overlaps as undefined. Exceptions, alignment faults, memory
permissions, system registers, optional architectural features and
instructions outside the table are outside its scope.

From the repository root, run

```sh
sh compiler/model/a64-test.sh
```

The command certifies the three books in logic mode and runs ACL2
checks for reserved encodings, little-endian memory, address wraparound
and the run stops. Add `--certify-only` to run just those checks and
certification.

The processor comparison runs on macOS on Apple silicon. It uses
`build/runner/boymoo-run` and `build/export/library.statements` to run
the compiler's assembler, `SYSTEM-CODE` and `MACHO-EXECUTABLE` on a
test `rt:start`. The resulting executable maps a buffer with `sys:map`,
loads registers and sets NZCV from words in its code, and runs each
case. It writes the final general-purpose registers other than X18,
SP, NZCV, the capture address and the test buffer to standard output
with `sys:write`. ACL2 uses the reported code and buffer bases to
compare those values with the model. The certificates, executable and
logs are in `build/compiler/a64-model/`.

On 2026-11-26, `sh compiler/model/a64-test.sh` certified the three
books with ACL2 8.7, printed `A64 model checks passed.` and printed
`A64 processor and ACL2 agree in 7 cases.`
