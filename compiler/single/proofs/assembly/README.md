# A64 assembly and instruction execution

The books relate assembler items to the machine and kernel semantics.
An item offset is the sum of `a64-image-item-size` over the preceding
items. A label key may be a string, a number, a character, a symbol,
or a cons of label keys. A rank table assigns a distinct rational
number to each key. The order of the numbers agrees with the assembler's
key comparison. `assembly-ranking-p` checks this condition on the
finite table. [Assembler](../../../a64.lisp) [Proof foundations](../foundations/)

`assembly-executable-item-p` states the operand widths, instruction
alignment, displacement ranges, and pair-load and writeback overlap
conditions. It uses the association list of label offsets, so it can
be evaluated before a call to `a64-word`. A branch displacement is
signed and measured in instruction words. An ADR displacement is
signed and measured in bytes. An ADRP displacement is signed and
measured in 4,096-byte pages.

## Layout and bytes

| Theorem | Statement |
|---|---|
| `assembly-labels-after-prefix` | The reference label association list for a suffix starts at the initial offset plus the size of the prefix. |
| `assembly-layout-end-and-order` | With distinct and initially unbound labels, a valid rank table, natural item sizes, and a well-formed input table, the assembler returns the end offset, the reversed non-label items, and a well-formed label table. |
| `assembly-layout-label-lookup` | The actual hashed and balanced table returns the new label's offset when the label is present. A lookup for another ranked key returns its value in the input table. |
| `assembly-layout-entry-offset` | A defined entry name is resolved to its offset in the reference association list. |
| `assembly-table-text-less-by-number`, `assembly-compiler-label-order` | A numeric order represents the key comparisons for strings, `(:fn string)`, and `(:local natural)`. |
| `assembly-compiler-label-ranks-pass-check`, `assembly-layout-input-for-compiler-labels` | Distinct keys of those forms admit an explicit rank table for layout from an empty table. |
| `assembly-key-order-trichotomy`, `assembly-key-order-transitive` | The assembler compares distinct label keys in a strict total order, including nested conses and complex rationals. |
| `assembly-key-ranks-pass-check`, `assembly-layout-input-for-distinct-labels` | Counting the smaller keys in a finite list constructs a rank witness for distinct keys. A natural starting offset, natural item sizes, and distinct label keys suffice for layout from an empty table. |
| `assembly-layout-lookup-from-empty`, `assembly-label-offset-bounds` | The actual table gives an existing key's offset and returns NIL for an absent key. Every defined offset is between the starting and ending offsets, inclusive. |
| `assembly-write-chunks-characters` | Flattening the fragment buffer produces the concatenation of the item characters in file order, followed by the supplied suffix. |
| `assembly-byte-padding-bounds` | A byte string gains between zero and three padding bytes. The byte item specifies zero for every padding byte. |
| `assembly-item-character-count` | With well-formed data items, every item contributes its declared layout size. A quad contributes eight little-endian bytes, and an image contributes its fragments in order. |
| `assembly-flattened-image` | The image from `a64-assemble-image` contains the concatenated item characters and has the declared size and the requested entry offset. |
| `assembly-image-well-formed` | The assembled fragment lengths sum to the size in the image record. |
| `assembly-assemble-image-for-distinct-labels` | A properly formed item list with distinct keys, well-formed data, and a defined entry supplies the image, byte concatenation, size, and entry conclusions. |

## Decoding

The theorem names in the table are in package `BOYMOO-PROOFS`.
Each identifies the instruction record returned by `proof-decode` for
the indicated word. The operands in that record are the operands of
the instruction semantics in the machine model. The single-word
immediate arithmetic rules describe the words returned by `a64-word`.
The expansion rules describe the pair selected by the image emitter.
`assembly-specified-instructions` gives the decoded record or pair
for each executable item using the operands and the reference label
offsets. `assembly-executable-item-decodes` proves this specification
from the independent operand checks and agreement of the label lookup.

| Theorem | Decoded operation |
|---|---|
| `assembly-decode-movz`, `assembly-decode-movn`, `assembly-decode-movk` | Move a 16-bit immediate at one of the four halfword positions. |
| `assembly-decode-mov`, `assembly-decode-mov-sp` | Copy through the zero-register logical form or the stack-pointer immediate-add form, respectively. |
| `assembly-decode-add`, `assembly-decode-sub`, `assembly-decode-adds`, `assembly-decode-subs`, `assembly-decode-cmp`, `assembly-decode-cmn` | Add or subtract an immediate, with the opcode determining whether to set flags and whether register 31 in the destination denotes the stack pointer. |
| `assembly-decode-add-reg`, `assembly-decode-sub-reg`, `assembly-decode-adds-reg`, `assembly-decode-subs-reg`, `assembly-decode-cmp-reg`, `assembly-decode-neg` | Register arithmetic with the specified left shift and zero-register interpretation. |
| `assembly-decode-and-reg`, `assembly-decode-orr-reg`, `assembly-decode-eor-reg`, `assembly-decode-ands-reg`, `assembly-decode-tst-reg`, `assembly-decode-mvn` | Register logic, including the flag-setting test and the inverted source of MVN. |
| `assembly-decode-and-mask`, `assembly-decode-tst-mask`, `assembly-decode-and-mask-discard` | Logic with the low-bit mask and the discarded destination interpretation of `:and-mask` with register 31. |
| `assembly-decode-lsl`, `assembly-decode-lsr`, `assembly-decode-asr` | The bitfield encodings of the three immediate shifts, with the decoded masks specified in the conclusions. |
| `assembly-decode-lslv`, `assembly-decode-lsrv`, `assembly-decode-asrv`, `assembly-decode-clz` | Variable shifts and the leading-zero count. |
| `assembly-decode-mul`, `assembly-decode-smulh`, `assembly-decode-msub`, `assembly-decode-sdiv`, `assembly-decode-udiv` | Multiply, signed high multiply, multiply-subtract, and the two quotient operations. |
| `assembly-decode-csel`, `assembly-decode-cset`, `assembly-decode-cset-al` | Conditional selection, conditional increment with zero sources, and the move of 1 for the always condition. |
| `assembly-decode-ldr`, `assembly-decode-str`, `assembly-decode-ldrb`, `assembly-decode-strb` | Loads and stores with an unsigned scaled offset. |
| `assembly-decode-ldr-reg`, `assembly-decode-str-reg`, `assembly-decode-ldrb-reg`, `assembly-decode-strb-reg` | Loads and stores with an unscaled 64-bit register offset. |
| `assembly-decode-ldp`, `assembly-decode-stp`, `assembly-decode-ldp-post`, `assembly-decode-stp-pre` | Pair loads and stores with signed scaled offsets and the specified writeback mode. |
| `assembly-decode-b`, `assembly-decode-bl`, `assembly-decode-b-cond`, `assembly-decode-cbz`, `assembly-decode-cbnz` | Branches with signed displacements, including negative displacements and the link bit of BL. |
| `assembly-decode-br`, `assembly-decode-blr`, `assembly-decode-ret`, `assembly-decode-svc` | Register branches, return through register 30, and the system call immediate. |
| `assembly-decode-adr`, `assembly-decode-adrp` | Form an address from the current PC or its page, respectively. |
| `assembly-decode-zero-source-arithmetic`, `assembly-decode-zero-source-compare` | The two-instruction expansions for zero-source `:adds`, `:subs`, `:cmp`, and `:cmn`. |
| `assembly-decode-far-address-item` | The page address and the following ADD or discarded-register move emitted for `:adr-far`. |

## Placement and execution

| Theorem | Statement |
|---|---|
| `assembly-linked-image-places-item` | The mapped image contains an item's exact characters at image base plus item offset. |
| `assembly-load-serialized-word` | The model loads a little-endian word from those characters. |
| `assembly-linked-item-instructions` | A linked item has all its emitted words at executable addresses. Fetch there gives the decoded instruction list. |
| `assembly-linked-specified-instructions` | A specified list of decoded instructions can be substituted for that list using the decoding rules. |
| `assembly-linked-executable-item-instructions`, `assembly-linked-program-item-instructions` | The operand checks for a selected item or for the whole image imply placement of the specified instructions at the item's offset in the mapped image. |
| `assembly-linked-single-instruction-step` | At a live world with the specified PC and permitted data accesses, the checked step has the model's register, flag, memory, and PC effect for the placed instruction. |
| `assembly-linked-two-register-instructions-run` | A placed pair of register instructions takes two steps and reaches the cutpoint at the 64-bit PC plus eight, reduced modulo 2^64. The premises exclude cuts at either instruction. |
| `assembly-linked-executable-item-advance`, `assembly-linked-executable-item-to-cutpoint` | From the item's address, the checked model applies all the specified effects in order, including a system call's kernel effect. A live result at a cutpoint gives a segment when execution reaches it after the complete item. |
| `assembly-run-after-clear-prefix`, `assembly-segment-to-cutpoint`, `assembly-one-step-to-cutpoint`, `assembly-two-steps-to-cutpoint` | Runs compose across a prefix that encounters neither a stop nor a cutpoint. A segment reaches the selected cutpoint when its final state is live and at the selected address. |
| `assembly-straight-line-run` | A list of successive placed instructions with permitted accesses runs to its final cutpoint with the specified sequence of state updates. |
| `assembly-b-run`, `assembly-b-cond-run`, `assembly-cbz-cbnz-run` | Immediate branches reach the target or fall-through selected by the flags or the tested register. |
| `assembly-bl-run`, `assembly-blr-run`, `assembly-br-run`, `assembly-ret-run` | Branches through the stated destination reach its cutpoint. Calls also put the next sequential PC into register 30. |
| `assembly-discarded-and-effect`, `assembly-cset-effect`, `assembly-cset-al-effect`, `assembly-clz-effect`, `assembly-svc-event` | These instructions have the specified zero-register, conditional or constant move, bit count, and system call effects. |
| `assembly-bitfield-logical-left-effect`, `assembly-bitfield-logical-right-effect`, `assembly-bitfield-arithmetic-right-effect` | The decoded bitfield masks implement a left shift, an unsigned right shift, and a signed right shift, respectively. |
| `assembly-add-immediate-effect` | The immediate add reads and writes the stack pointer when the respective register field is 31. |
| `assembly-far-address-effect`, `assembly-linked-far-address-effect` | At a 4,096-byte aligned image base, the two instructions write the absolute target address reduced modulo 2^64 for an ordinary destination. A destination of 31 discards the result. |
| `assembly-zero-source-add-effect`, `assembly-zero-source-subtract-effect`, `assembly-zero-source-discard-effect` | The two-instruction sequences compute the addition or subtraction of the immediate with a zero left operand, including flags. For a discarded destination, the sequences update the flags and the PC. |
| `assembly-linked-expansion-machine-effect`, `assembly-linked-zero-source-effect` | Both words of an expansion are fetched and executed. The zero-source arithmetic or compare reaches the stated result and flags in two checked steps. |

## Compiler item bounds

A fixed field is a condition on an instruction item's operands.
`assembly-fixed-item-fields-p` checks these conditions for
one instruction item at offset zero with a zero displacement. The
layout still has to supply an aligned item address and a defined label
for each reference. `assembly-resolved-item-addresses-p` checks those
conditions, including word alignment of branch targets.

| Theorem | Statement |
|---|---|
| `assembly-branch-field-fits-small-image`, `assembly-address-fields-fit-small-image` | The signed branch, byte-address, and page-address fields fit when the referenced offsets are below 2^20 and the branch operands have word alignment. |
| `assembly-item-fields-fit-small-image`, `assembly-image-program-for-small-image` | For an image smaller than 2^20 bytes, fixed fields and resolved and aligned addresses establish the executable checks for one item or for every item of a valid layout. |
| `assembly-fixed-fields-of-system-and-runtime` | The Linux and macOS system templates and the runtime satisfy the fixed item checks. |
| `assembly-fixed-fields-of-gen-emit` | Adding items to the reversed code accumulator preserves the fixed item checks. |
| `assembly-fixed-fields-of-gen-load-high`, `assembly-fixed-fields-of-gen-load-word`, `assembly-fixed-fields-of-gen-load-datum` | The immediate and tagged datum emitters preserve the fixed fields under the stated register, integer, and shift conditions. |
| `assembly-fixed-fields-of-gen-address`, `assembly-fixed-fields-of-gen-frame-word`, `assembly-fixed-fields-of-gen-argument-registers`, `assembly-fixed-fields-of-gen-copy-arguments` | Address calculation, frame loads, and argument transfer preserve the fixed fields under the stated offset and register bounds. |
| `assembly-fixed-fields-of-gen-defined-call`, `assembly-fixed-fields-of-gen-prologue`, `assembly-fixed-fields-of-gen-stack-helpers`, `assembly-fixed-fields-of-gen-routine`, `assembly-fixed-fields-of-gen-simple` | Calls, prologues, stack operations, routine expansions, and simple values preserve the fixed fields under their operand premises. |
| `assembly-fixed-fields-of-gen-functions`, `assembly-compiled-items-fixed-fields` | The compiler assembles a list satisfying the fixed item checks when the generated definition bodies, the system, and the static image meet the stated checks. |
| `assembly-fixed-fields-of-gen-term`, `assembly-fixed-fields-of-gen-args`, `assembly-fixed-fields-of-gen-lambda-args` | Joint induction over term and argument generation establishes the fixed fields from typed lookups and natural counters. Lambda argument generation also preserves the slot types of the body scope. |
| `assembly-generated-bodies-for-typed-constants`, `assembly-compile-items-fixed-fields-from-inputs` | A constant index with integer words or immediate integers supplies the definition body checks. The resulting items pass the fixed checks for either system template. |
| `assembly-image-program-with-final-data` | When references resolve in a valid prefix of ordinary items, the 1 MiB bound applies to that prefix. Appending a sized static image preserves the executable checks. |

## Generated labels and compilation

A local label has the form `(:local natural)`. The generator advances
a serial counter as it reserves local labels. A definition reserves two
serials for its prologue before generating its body. A definition's
function label has the form `(:fn name)`, and the system and runtime
label names are strings. The compile prefix ends with `data:static`.
The static image is the final item.

| Theorem | Statement |
|---|---|
| `assembly-gen-term-label-origin`, `assembly-new-term-labels-are-local` | Each new label in a term's code belongs to the serial interval allocated by the generator. Starting from an empty accumulator, every emitted label is local. |
| `assembly-gen-term-keeps-labels-distinct` | The generator preserves distinct accumulator labels and advances their serial bound. |
| `assembly-gen-term-reference-origin`, `assembly-gen-functions-reference-origin` | An unresolved reference comes from the accumulator, a routine named in the primitive or prelude tables, the undefined-function stop, or a definition named by the arity index. Function prologues can also refer to the runtime's growth and depth checks. |
| `assembly-gen-functions-local-layout`, `assembly-gen-functions-global-labels` | Local labels remain distinct across definitions. The global labels are the accumulator's labels and the emitted function labels, including `rt:entry` for the selected entry. |
| `assembly-index-lines-cover-arity-lookups`, `assembly-index-lines-returns-distinct-definition-names` | Starting with empty tables, indexing the compiler's text lines gives distinct effective definition names and a definition for every non-NIL arity lookup. |
| `assembly-read-compiler-inputs-definition-checks` | When an entry is present and its arity is admissible, entry-wrapper insertion supplies the entry definition, preserves distinct names, and preserves coverage of the arity index. |
| `assembly-compile-prefix-distinct-labels`, `assembly-compile-prefix-resolves-references` | The compiler's system, runtime, generated definitions, and final data label have distinct labels and resolve every reference under the stated input conditions. |
| `assembly-compile-items-pass-image-checks`, `assembly-bounded-compiler-text-passes-image-checks` | The compiler's items satisfy layout and executable field checks for either system template when the code prefix is shorter than 1 MiB, the constant index is typed, and the final static image is sized. The text theorem derives the entry, definition-name, and arity-coverage premises from indexing. |
| `assembly-compile-text-serializes-input-items` | The logical `compile-text` result is the selected ELF or Mach-O serialization of the assembled compiler items. |

## Source input and static image

The source tree weight counts each cons and atom once and adds the
lengths of strings in the tree. The bound uses 128 bytes per unit of
body weight and another 128 bytes per effective definition. It
includes the selected system and runtime templates and the effective
entry definition, including a wrapper when required. The bound can
be computed from the reader and index before generating instructions.

| Theorem | Statement |
|---|---|
| `assembly-accepted-atom-scan-agrees`, `assembly-accepted-token-scan-agrees`, `assembly-accepted-datum-scan-agrees` | An accepted scan supplies the compiler's next input position through the corresponding delimiter, token, or quoted datum. |
| `assembly-accepted-line-reader-agrees`, `assembly-accepted-program-reader-agrees` | For a successful checked read, the parser returns the same lines as the compiler reader. The checked reader returns a rejection flag on malformed lexical input. |
| `assembly-accepted-definition-index-agrees`, `assembly-accepted-line-index-agrees`, `assembly-accepted-attachment-resolution-agrees`, `assembly-accepted-text-index-agrees` | Checked indexing and attachment resolution supply the same effective definitions, arities, terminal targets, packages, entry, and target as the compiler whenever the checks succeed. |
| `assembly-accepted-formals-agree`, `assembly-accepted-generation-agrees`, `assembly-accepted-definition-generation-agrees` | Successful checked generation supplies the compiler's bindings, code, stack high-water mark, and label serials on the relevant results. The checks cover variable and datum lookups, lambda and conditional shape, call arities, and both bodies of an `mbe`. |
| `assembly-generation-size-from-source-tree`, `assembly-generation-size-from-definitions` | Generation preserves an accumulator free of image items and adds at most the stated budget for a term or a list of definitions. |
| `assembly-compile-prefix-size-from-definitions`, `assembly-compiler-text-prefix-size-from-source`, `assembly-source-bound-implies-compiler-bound` | The source bound dominates the emitted prefix size. When the source bound is below 1 MiB, the emitted prefix meets the same limit. |
| `assembly-data-write-size`, `assembly-static-image-from-sized-block` | Static serialization preserves the byte count of padded strings and eight-byte words, including tagged immediate integers. A sized block with its ten-word header supplies the image relation. |
| `assembly-canonical-integer-token-parses` | A canonical signed decimal token supplies an integer to static numeric serialization. |
| `assembly-static-block-sizes-data-number`, `assembly-static-state-collects-datum`, `assembly-static-state-collects-program` | Numeric data, nested quoted data, and program constants preserve the size and datum conditions under the corresponding syntax and decoder premises. |
| `assembly-static-package-state-is-sized`, `assembly-data-build-produces-sized-image-and-typed-index` | Package collection and the static-data builder establish the size and type conditions from the declared packages and the parsed program's static-data conditions. |
| `assembly-static-text-supplies-image-and-constants`, `assembly-source-layout-inputs-pass-image-checks` | Accepted reader input with the stated entry, data, and source-size conditions supplies the compiler's image checks for both targets. |

## Checked machine state and memory

| Theorem | Statement |
|---|---|
| `assembly-loader-preserves-register-file`, `assembly-checked-advance-preserves-register-file`, `assembly-checked-run-preserves-register-file` | Loading and checked Linux runs preserve an association list of registers. |
| `assembly-svc-event-identifies-instruction`, `assembly-valid-register-file-supplies-item-access` | With that register-file invariant, a system call event identifies a system call instruction, and the memory access premise suffices for the item execution rules. |
| `assembly-standard-executable-span-protected`, `assembly-writable-span-disjoint-from-code` | An executable span in a valid region list is disjoint from each covered write span. |
| `assembly-add-disjoint-writable-region-preserves-code-protection`, `assembly-unmap-preserves-code-protection` | Adding a disjoint writable region or removing a writable span preserves the protection of the executable span. |
| `assembly-model-store-writes-only-its-span`, `assembly-cleared-span-keeps-other-bytes`, `assembly-store-bytes-keeps-other-bytes` | Word stores, cleared memory intervals, and byte-list stores preserve bytes outside the specified spans. |
| `assembly-checked-access-covers-instruction-writes`, `assembly-checked-instruction-preserves-protected-byte` | The checked access covers the instruction's write span. A checked non-system-call step preserves bytes in protected executable memory with a valid register file and integer pair offsets. |

## Linux loading

| Theorem | Statement |
|---|---|
| `assembly-elf-image-file` | For an image with a sized fragment list, an aligned entry with four bytes available, and a file end at or below 2^63, the compiler writes an ELF file accepted by the model. Its entry, length, and image bytes have the stated values. |
| `assembly-loaded-file-places-characters`, `assembly-fragments-from-placed-characters` | Loading a file into cleared memory establishes the byte placement relation for its characters and for the image fragments they represent. |
| `assembly-linux-loader-maps-elf-image`, `assembly-linux-loader-zero-page-tail` | With the loader's stack, region, and input premises, Linux loading places the image in an executable region, initializes the PC to the entry address, and supplies zero bytes from the file end up to the rounded page boundary. |
| `assembly-load-linked-linux-image` | Assembling and loading an image establishes `proof-linked-image-p`. |
| `assembly-compile-items-prefixed-by-system`, `assembly-linux-entry-in-compile-items` | The compiler places the system items before the remaining items. The Linux entry label has image offset 108. |
| `assembly-compile-text-elf-of-linux-items`, `assembly-compiled-start-maps-linux-items` | The file obtained from Linux compiler text is the ELF serialization of its assembled items. With the image layout, size, and loader premises, `proof-compiled-start` establishes the linked image and starts at `os:main`. |
| `assembly-compiled-start-places-linux-instructions` | When the compiler output meets the image checks, the world from `proof-compiled-start` has every specified instruction at its compiled address. |
| `assembly-bounded-linux-compiled-start` | Bounded compiler text satisfies the image checks, and the Linux start world meets the linked-image relation and starts at image offset 108 under the file-size and loader premises. |

## Mach-O loading and signature

The process handoff supplies the initial registers, the writable
stack, and other modeled regions. The base of `__TEXT` is a
16,384-byte-aligned address at or above the preferred base. The model
installs `__TEXT` with execute permission and starts at the offset
given by the main-entry load command. A hash slot holds the 32-byte
digest of one 4,096-byte file page in `__TEXT`. The pages cover the
header, the assembly image, and the zero padding. The proofs compare
the stored digests with the compiler's SHA-256 function applied to
the contiguous page bytes.

| Theorem | Statement |
|---|---|
| `assembly-macho-segment-rounding`, `assembly-macho-header-fields` | Segment lengths round up to a 16,384-byte multiple. The header supplies the measured text span, entry, read and execute protections, and signature location. |
| `assembly-macho-signature-size-formula`, `assembly-macho-signature-fragments-size` | The signature has 128 bytes plus 32 bytes per hash slot, and its emitted fragment lengths sum to that size. |
| `assembly-macho-image-file-characters`, `assembly-macho-file-length-and-header`, `assembly-macho-file-text-and-signature` | The file contains the fixed header, the precise assembly fragments, the zero text padding, and the signature fragments. Its header offsets and length agree with these parts. |
| `assembly-sha256-message-length`, `assembly-sha256-range-uses-explicit-message` | Hashing a string range with implicit trailing zeroes gives the same digest words as hashing the explicit message of the stated length. |
| `assembly-sha256-page-pieces-exact`, `assembly-sha256-page-hashes-contiguous-bytes` | The fragment cursor copies the exact available page prefix and advances over it. The digest covers the contiguous page with zeroes filling any space after the last byte. |
| `assembly-macho-page-digest-is-sha256`, `assembly-macho-code-slots-hash-flat-pages`, `assembly-macho-digests-with-explicit-zeroes` | The file-order slots contain SHA-256 digests of consecutive pages. Writing the trailing page zeroes explicitly preserves the digests. |
| `assembly-macho-signature-prefix-contains-header-hash`, `assembly-macho-signature-hash-tail`, `assembly-macho-file-stores-text-page-digests` | Beginning 115 bytes into the signature, the file stores the digests of every `__TEXT` page in order, starting with the header page, followed by 13 zero bytes. |
| `assembly-macho-emitted-file-p`, `assembly-macho-loader-maps-text` | The emitted file meets the structural header checks. Loading its executable segment places the exact image bytes, sets the PC to the declared entry, and creates an executable region. |
| `assembly-load-linked-macho-image`, `assembly-bounded-macho-compiled-start` | The Mach-O model establishes the linked-image relation at the supplied base. For bounded compiler text the entry is `os:main` at image offset 144. |

The full handoff model maps the complete file, including the signature
in `__LINKEDIT`. It uses the supplied stack and registers, installs the
mapped program counter, and associates a reply list with the Darwin
system call interface. A reply contains either a success value or a
positive error number. The Darwin execution model uses a data-access
view of read-only mappings and keeps the original permissions for
instruction fetch. Anonymous mappings avoid the address range reserved
by `__PAGEZERO`.

| Theorem | Statement |
|---|---|
| `assembly-macho-handoff-loads-complete-file`, `assembly-macho-handoff-zeroes-linkedit-tail` | The handoff maps the exact file bytes, preserves the incoming registers, sets the entry PC, and zeroes the part of the last mapping beyond the file. |
| `assembly-macho-linkedit-is-read-only`, `assembly-macho-handoff-places-signature` | Each positive subspan of the link-edit mapping admits reads and excludes writes and instruction fetch. The signature bytes start at the mapped end of `__TEXT`. |
| `assembly-macho-handoff-links-assembled-image` | The full handoff establishes the shared linked-image relation and entry PC for the assembled image. |
| `assembly-darwin-step-from-instruction`, `assembly-darwin-svc-step-uses-x16` | A placed instruction with permitted accesses has its specified effect. For SVC immediate `#x80`, the kernel selects the operation from X16. |
| `assembly-darwin-return-shape`, `assembly-darwin-carry-conditions`, `assembly-darwin-exit-svc` | A returning call consumes a reply, updates X0 and carry, and advances the PC. The carry conditions distinguish success from an error. An exit observes the status in X0. |
| `assembly-darwin-map-respects-pagezero` | The modeled anonymous mapping operation rejects a success reply in the reserved address range. |

## Premises and open goals

Each checked memory operation requires the permissions in
`proof-instruction-access-p`. The register-only world rules rule out
the literal atom `:svc` as the register file. Association lists
satisfy this condition. `proof-instruction-effect` tells a system call
by its instruction, and `assembly-malformed-register-file-is-no-system-call`
shows a discarded MOVZ whose resulting machine begins with `:svc` and is
still taken as a machine. The condition can therefore be removed from
the register-only world rules and from `assembly-item-access-p`.

The source layout theorem uses checked lexical input, indexing, and
attachment resolution. It also requires the existence and arity of an
entry, syntax and decoder conditions for static data, and the source-size
bound. The remaining source obligation is agreement between the program
format in a source ACL2 world and the successful checks, including
operational acceptance by all of static-data collection and the
premises of the checked generator. The data builder theorems establish
the structural image and index types. The source value interpretation
of the static data and the routine contracts are needed to connect
the compiled run to source evaluation.

The remaining native startup obligation is to relate dyld's acceptance
of the ad hoc signature and its register, stack, and mapping handoff
to the modeled inputs. Sharing the full Mach-O rules through the
foundations would require a read-only mode in `proof-region-p` and
`proof-region-allows-p`. It would also require a Darwin SVC transition
alongside the Linux transition, with dispatch from X16 for immediate
`#x80` and Darwin's carry and X0 results.

## Certification

Run from the repository root.

```sh
SBCL_USER_ARGS='--dynamic-space-size 2500' sh compiler/single/proofs/certify.sh --foundations
sh compiler/single/proofs/assembly/certify.sh
```

On 2026-11-26, ACL2 8.7 certified the foundations and all 71 assembly
books in logic mode. The foundations command printed
`Compiler proof foundations certified.` The assembly command printed
one certification line per book, ending with
`Certified compiler/single/proofs/assembly/checks.lisp.` The ACL2 logs and
certificates are under `build/compiler/single/proofs/`.

```sh
sed -n '/^:PASSED/p' build/compiler/single/proofs/assembly/checks.out
```

On 2026-11-26, this command printed five `:PASSED` lines. The checks
compile a Linux echo program to a 50,256-byte ELF, load the image, and
run it through two short writes to exit 0 with the two bytes of `Az`
on standard output. The address-boundary check uses both an ordinary
destination and register 31. It checks the two-word expansion when
the target address and the final PC wrap to zero. A program with a
conditional, a lambda, and a replaced definition passes the layout
checks for both targets. Its 66,176-byte Mach-O file loads at a slid
base, has zero text padding, and branches from file offset `0x1090`
to `rt:start` with the return address in X30.

The reader check accepts the conditional and lambda program with the
compiler's parsed lines and rejects a line with an unclosed list. The
conditional and lambda program also passes the checked generator and
source layout conditions for its two targets. The input checks resolve
an acyclic attachment, reject an attachment cycle, accept a signed
decimal integer, and reject a negative zero spelling.
The full Mach-O handoff exercises a read-only mapping for the
signature. The Darwin model runs the echo program through short
writes to exit 0 with `Az`. An error on the second write instead
leaves `A` on standard output, reports the output error on standard
error, and exits 2.
