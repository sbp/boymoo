# Compiler pass proofs

From the repository root, run `sh compiler/proofs/certify.sh` with ACL2 on
`PATH`. The command stages the compiler books, the Core and machine
models, and the proof books in `build/compiler/proofs`. Its logs and
certificates stay there. Proof book certification uses
`:skip-proofs-okp nil`, `:defaxioms-okp nil` and `:ttags nil`.

On 2026-11-27, `sh compiler/proofs/certify.sh` succeeded with ACL2 8.7 and an
empty `build/compiler/proofs` directory. The 24 proof books cover P0 through P9
and contain 194 theorem events, including local lemmas, and 39 executable
assertions.

## The reader, the data builder, the assembler and the executables

Four more directories hold proofs about the books of the compiler
outside its passes: the reader, the index, the data builder, the
assembler and the writers of executables. They are certified apart from
the books above, by `certify-sets.sh`.

| Directory | Books | Subject |
|---|---|---|
| [`foundations/`](foundations/) | 6 | What the other three share: spans and the decoding and stepping of the A64 model (`machine.lisp`); memory regions, the world of a process and the Linux system calls (`kernel.lisp`); the loader of Linux ELF files (`loading.lisp`); the words and object records that stand for ACL2 values (`values.lisp`); the layout of the heap and of the static image, and the maps of objects and constants to ACL2 values (`heap.lisp`); and linked images, runs and Core programs, with the books of the compiler that they concern (`interfaces.lisp`). |
| [`assembly/`](assembly/README.md) | 48 | The assembler of `a64.lisp`: the layout of items, and the decoding and execution of each instruction it encodes; the reader and the indexer against checked versions of them; the writing of static data; and the ELF and Mach-O files, their loading, and the Mach-O code signature. |
| [`data/`](data/README.md) | 63 | The data builder of `data.lisp`: the image it writes, the objects in it and the ACL2 values that the machine reads from them; and the reader's spans, the index and the resolution of attachments. |
| [`linux/`](linux/README.md) | 5 | The ELF file of `linux.lisp`, the world that the loader builds from it, and the system call wrappers up to their SVC. |

From the root of the repository, with ACL2 8.7 found as `acl2` on the
`PATH`:

```
sh compiler/proofs/certify-sets.sh
sh compiler/proofs/certify-sets.sh --foundations
sh compiler/proofs/certify-sets.sh --books SET BOOK ...
```

With no argument it certifies the compiler books `a64`, `read`, `index`,
`data`, `sha256`, `macos` and `linux`, the model books `a64-state`,
`a64-decode`, `a64` and `core`, and the foundations, in
`build/compiler/proofs/sets/`, and then each set by the `certify.sh` of
its directory, which names its books in order. With `--foundations` it
certifies the foundations alone, and with `--books` the books named, of
one set, once the foundations are certified. Like `certify.sh`, it uses
`:skip-proofs-okp nil`, `:defaxioms-okp nil` and `:ttags nil`.

On 2026-11-28, `sh compiler/proofs/certify-sets.sh` printed `Proof
foundations certified.` and a `Certified` line for each of the 133
books, and took 157 seconds. The three sets are 116 books of 24,336
lines, and the foundations 1,685 lines (`cat
compiler/proofs/{assembly,data,linux}/*.lisp | wc -l` and `cat
compiler/proofs/foundations/*.lisp | wc -l`, the same day).

## Semantics

The L1 entry points are `l1-eval` for an expression and `l1-call`
for a named call. They use the primitive and prelude semantics of
`compiler/model/core.lisp`. A constants table associates boxed words with
ACL2 data. Each result is a Core value, `:no-value`, `:out-of-fuel`, or
`:malformed` for a missing part of a model input. The `:no-value` outcome
records termination without a value. Error message formatting is outside
the observation.

`l1-program-p` checks scopes, distinct binder numbers within a
definition, and call arities. The QIR books use `qir-a-p`, `qir-m-p`
and `qir-l-p` from `compiler/qir.lisp`.

`qir-run` interprets a call to a QIR function. For QIR-A, the
environment contains ACL2 data and phis read a snapshot of the predecessor
environment. QIR-M and QIR-L use words. The abstract heap contains bytes,
a next allocation address, and the ACL2 data represented by its published
words. Supply the bytes and datum associations for any static objects
the program reads. A `:rt` whose target appears in the QIR function list
executes that function. Other modeled runtime calls apply Core routine
semantics to decoded arguments and encode a returned value. QIR-L tracks
each frame's value-stack slots after they are first written. Reading an
unwritten slot yields `:malformed`. The model uses stable heap offsets
under sufficient stack and heap resources.
`qir-observe` interprets a machine result through the final heap.

`mir-pure-result` covers immediate loads, moves, arithmetic, bit
operations and shifts. The register assignment proof also models the
writes permitted across compiled and runtime calls.

## Model lemmas

| Theorems | Statement |
|---|---|
| `model-constant-of-nil`, `model-constant-of-t` | The words 34 and 58 yield the two corresponding Core symbols. |
| `model-lookup-of-alist-update` | Looking up a key after a write reads the new binding for that key and the previous binding for other keys. |
| `model-word-as-mod`, `model-word-range`, `model-word-is-natural` | Word normalization computes the remainder modulo 2<sup>64</sup> and yields an unsigned 64-bit integer. |
| `model-word-in-range`, `model-word-idempotent`, `model-integer-word-canonical`, `model-integer-word-is-natural`, `model-integer-word-in-range` | Canonical words are fixed points of normalization. An integer word is canonical and in the unsigned word range. |
| `model-negative-word`, `model-signed-of-word`, `model-signed-of-signed-64` | The negative word formula uses addition of 2<sup>64</sup> in its stated range. Signed interpretation commutes with normalization and gives the original signed value in range. |
| `model-immediate-signed-word`, `model-immediate-word-is-odd`, `model-constant-of-immediate-integer` | A signed 63-bit integer is represented by the odd word of `2n + 1` and decodes to that integer for any constants table. |
| `model-word-and-in-range`, `model-word-and-is-canonical`, `model-word-equality-computes-flag` | Bitwise AND produces a canonical word. Word equality produces the flag for equality of the normalized operands. |
| `l1-eval-step-more-fuel`, `l1-eval-of-constant` | Increasing fuel preserves a non-exhausted result. A constant with fuel is interpreted by the datum decoder. |
| `qir-graph-entry-has-no-phis` | The compiler's graph recognizer implies that the entry block has no phis. |

## Runtime routines in QIR

The tests and theorems call `rt-qir-functions` through a QIR-M `:rt`
instruction. They use the routine bodies after critical-edge splitting.

- `rt-equal-on-identical-words` proves that an identical pair of
  words returns word 58 and preserves the heap.
  `rt-equal-distinct-unboxed-words-return-nil` proves that unequal
  canonical words return word 34, the representation of NIL, with the
  heap preserved when the first tag rules out a cons or a header.
- `rt-equal-identical-datums-agrees-with-core` compares the decoded
  result with Core when the common input word represents a datum.
  `rt-equal-of-fixnums-agrees-with-core` covers all pairs of signed
  63-bit integers. The local `rt-immediate-integer-tag-is-odd`,
  `rt-immediate-integer-tags-exclude-pointers` and
  `rt-immediate-integer-words-are-injective` give the tag and distinctness
  facts used for unequal fixnums.
- `rt-equal-different-headers-return-nil` gives the early return on
  unequal readable headers. The local `rt-word-inequality-computes-flag`
  relates the machine comparison to word inequality.
  `rt-equal-of-different-length-strings-agrees-with-core` uses that path
  for two represented strings with different lengths.
- `rt-length-reads-string-header` gives the tagged count from a
  successful header read. `rt-length-of-represented-string-agrees-with-core`
  compares it with Core for any represented string whose header supplies
  its byte length. `rt-string-header-is-a-word`, `rt-string-header-fields`,
  `rt-word-with-tag` and `rt-length-encoding-is-immediate` are the
  local word and header equations.
- `rt-length-of-represented-list-agrees-with-core` covers proper lists
  with a readable spine ending in NIL and a readable NIL header. The
  length fits in a nonnegative fixnum, and the fuel bound grows with
  the length. `rt-length-loop-advances-over-cons` and
  `rt-length-loop-returns-count-at-nil` give the two loop transitions.
  `rt-length-loop-counts-represented-list` lifts them to the whole
  spine, and `rt-length-list-call-follows-loop-result` connects the
  runtime call to that loop. The local
  `rt-length-add-two-increments-encoded-count`,
  `rt-length-cons-leaves-next-loop-inputs` and
  `rt-list-spine-starts-with-nil-or-cons` give the counter, binding,
  and list entry facts.
- `rt-char-reads-indexed-byte` gives the returned character word for
  the in-range immediate-integer path. `rt-char-of-represented-string-agrees-with-core`
  compares the observation with Core for a nonnegative index below the
  length. Its premises include a readable byte matching the character
  in the represented string. `rt-fixnum-index-decodes`,
  `rt-unsigned-comparison-uses-word-order`,
  `rt-character-encoding-is-character-word`,
  `rt-character-word-decodes` and
  `rt-character-of-in-range-string-index` provide the local index and
  character equations.
- `rt-char-fixnum-index-outside-string-returns-nil` gives the machine
  result when the clamped index is at or past the string length.
  `rt-char-of-represented-string-past-end-agrees-with-core` uses the
  local `rt-nth-past-end-is-nil` and `rt-core-char-past-end-is-nil`
  to match the logical result of Core at an out-of-range nonnegative
  fixnum. `rt-char-of-represented-string-negative-index-agrees-with-core`
  covers negative fixnums. Its local
  `rt-negative-fixnum-index-clamps-to-zero` and
  `rt-core-char-negative-index-is-first` identify the zero index used
  by both evaluations. The negative-index theorem uses the first byte
  for a nonempty string and NIL for an empty one.

The runtime theorems use the evaluator's depth-based fuel. They require
at least 14 for the identical-word path, 32 for the fixnum equality and
string length results, 24 plus nine per cons for list length, and 50 for
character access. The unequal-header path uses at least 64. Executable
examples cover distinct string objects, a list comparison, a list length,
and dispatch to a runtime label supplied by the native model. A P4 example
uses primitive expansion and evaluates both outcomes of a string equality
branch through the QIR runtime. General
comparison of boxed data, `LENGTH` on improper lists, and `CHAR` with
non-fixnum indices remain proof obligations.

## Theorems about the passes

Each pass book includes the book that defines the corresponding compiler
functions.

| Pass | Theorems and scope |
|---|---|
| P0, reader, index and data | `p0-read-lines-keeps-accumulator` proves that extending the reader's accumulator appends the extension to a nonempty result. `p0-resolve-chain-uses-cache` gives the resolved target and original cache for a completed cache hit. `p0-cached-list-constant` gives the original data state for a cached list constant. `p0-write-immediate-integer` gives the immediate descriptor and preserves the data block in the signed 63-bit range. |
| P1, resolution | `p1-formal-number-count` and `p1-formal-number-at-index` give the length and consecutive numbers of the formals. `p1-immediate-constant-word`, `p1-resolved-variable` and `p1-resolved-quote` give the tagged word and the resolved variable and quote forms. `p1-resolved-variable-agrees-with-core` and `p1-resolved-quote-agrees-with-core` give Core results under the corresponding environment or constant-table agreement. `p1-resolved-mbe-selects-logical-term` identifies the term selected in logic mode. `p1-resolved-if` gives the resolved conditional and fresh number, and `p1-resolved-if-agrees-with-core` composes the three subterm agreements. `p1-conditional-fragment-keeps-numbering` and `p1-conditional-fragment-preserves-evaluation` prove numbering and evaluation for trees of variables, quotes and conditionals under the binding and literal correspondence premises. The local `p1-zero-fuel-outcomes` supplies the zero-fuel case. |
| P2, simplification | `p2-simplify-nil-test` gives the chosen simplification and fresh number for a literal NIL test. `p2-simplify-nil-test-preserves-literal-result` covers the case of a literal false arm. `p2-fold-reflexive-equality-preserves-result` folds equality of two occurrences of a represented constant. `p2-unused-constant-binding-preserves-literal-result` covers an unused constant binding with a literal body. These evaluation results assume sufficient fuel and a represented value for each eliminated argument. |
| P3, lowering | `p3-lower-constant-definition` gives the instruction-free entry and return jump of a constant definition. `p3-parameter-count` gives the number of generated parameters. `p3-lower-constant-branch` gives the result of lowering the selected branch of a literal test. The local `p3-low-bits-of-a-word` applies the normalization identity to canonical test words. `p3-constant-definition-preserves-value` equates the result of a call to a constant definition and its lowering. `p3-nullary-constant-function-is-qir-a` establishes well-formedness for a nullary constant function. |
| P4, primitive expansion | `p4-copy-uses-current-substitution` identifies the emitted copy. `p4-bad-atom-records-nil-substitution` gives the replacement recorded for `BAD-ATOM<=`. `p4-bad-atom-expansion-agrees-with-primitive` relates that replacement to the Core result when the substitution map is initially empty. `p4-nil-branch-is-not-taken` shows that the original and transformed branch on NIL both follow the false edge. |
| P5, QIR optimization | `p5-optimizer-word-is-model-word` relates normalization in the optimizer to the semantics. `p5-folds-addition-as-word-operation` gives the sum of two unsigned words. `p5-folds-arithmetic-and-comparison-word-operations` covers addition, subtraction, multiplication, exclusive or, shifts, comparisons and overflow tests. `p5-signed-word-agrees`, `p5-overflow-test-agrees` and the local `p5-signed-word-is-integer` give the signed interpretation and overflow condition. `p5-constant-addition-replacement-preserves-value` and `p5-copy-replacement-preserves-value` relate the replacement operand to the original instruction result. `p5-unused-word-computation-has-no-effects` proves preservation of the heap and frame slots by a word instruction. `p5-dead-word-computation-is-removed` gives the filtering equation for an unmarked result. `p5-convert-diamond-uses-phi-arguments` identifies the select emitted for two empty branch arms and one join phi. `p5-select-agrees-with-single-phi` equates its result to the phi reading under the corresponding branch choice and operand values. |
| P6, frames and copies | `p6-phi-covers-predecessor` gives a binding for each covered predecessor. `p6-copy-snapshot-is-phi-bindings` equates the edge's pending copies with simultaneous phi evaluation. `p6-free-copy-does-not-change-sources` identifies the free destination condition. `p6-operand-of-unrelated-update`, `p6-operand-of-own-update` and `p6-snapshot-of-non-source-update` establish the effects of writes on operand readings. `p6-snapshot-of-saving-cycle-source` establishes snapshot agreement after saving and replacing a source. `p6-two-cycle-preserves-parallel-values` proves the emitted sequence for a swap of two temporaries reads the original pair of values. |
| P7, instruction selection | `p7-isel-word-is-model-word` and `p7-isel-signed-is-model-signed` identify the selector's word interpretations. `p7-copy-of-constant-preserves-value` and `p7-copy-of-temporary-preserves-value` cover immediate and register copies. `p7-add-immediate-preserves-value` and `p7-add-register-preserves-value` relate the selected additions to the QIR word result. The immediate addition uses an unsigned 12-bit immediate. |
| P8, register assignment | `p8-checked-block-has-consistent-live-in` relates a successful block check to the MIR backward transfer. `p8-preserved-home-after-clobber` and `p8-live-values-survive-call-clobbers` give preservation under writes permitted by the calling convention. `p8-live-values-survive-definition` and `p8-checked-instruction-result-stays-in-agreement` establish agreement after a destination write and after the combined clobber and write. `p8-live-temp-agrees-with-home` extracts a live value from that agreement. `p8-rewriting-a-live-operand-preserves-value` applies it to the allocator's actual operand rewrite. |
| P9, emission | `p9-move-between-registers`, `p9-move-from-register-to-spill-slot` and `p9-move-from-spill-slot-to-register` give the emitted A64 items for the three moves. `p9-move-x1-to-x0-decodes` identifies the decoded A64 instruction for that move. `p9-move-x1-to-x0-executes` proves that its execution copies the source word and preserves memory, flags and the stack pointer. The local `p9-a64-word-idempotent` supplies the word normalization equation. |

The general pass preservation results remain proof obligations. The
principal open parts include resolver scope changes and attachments,
inlining and graph rewrites, parallel-copy schedules with general
dependencies, relocation through collection, flags and control flow in
selection, and machine execution of frames, calls and emission.

## Loads moved out of loops

`p5-licm-prefix-op-is-total-and-pure` shows that the instructions
allowed to stay in a clean prefix succeed without changing the heap or
frame slots once their operands have been read. The local
`p5-licm-movable-load-after-barrier-is-guarded` establishes the test at
one instruction. `p5-licm-moved-load-after-barrier-is-guarded` applies
it to all newly moved loads when the prefix is already unclean.
`p5-licm-load-after-kept-barrier-is-guarded` covers a retained instruction
that ends a clean prefix. `p5-licm-new-load-outside-header-is-guarded`
extends the requirement over the blocks that `licm-blocks` scans with
the clean flag unset, using the local
`p5-licm-block-scan-excludes-unguarded-load`.
`p5-licm-unguarded-new-load-comes-from-header` uses that result for
the tail of the loop's block list to locate an unguarded move in the
header scan.

`p5-licm-split-at-any-prefix` gives the state for continuing a scan
after any instruction prefix. The local `p5-licm-prefix-remains-nontotal`,
`p5-licm-movable-with-nonnil-clean` and `p5-licm-scan-with-nonnil-clean`
prove the needed accumulator and flag equations.
`p5-licm-load-after-any-kept-barrier-is-guarded` applies the result to
the header scan. Once a retained instruction can stop, call or fault,
newly moved loads pass the guarded header recognition test.

`p5-licm-recognized-header-load-has-guard-shape` identifies the
`AND`, equality test, selection of the datum or NIL, and offset in the
compiler's recognizer. The local
`p5-licm-recognized-constant-is-the-model-word` relates the offset to
the operand evaluator. `p5-licm-header-load-cannot-fault` interprets
the tag selection and header read for the guarded pattern with a valid
header span. The local `p5-licm-list-of-length-two` and
`p5-licm-load-uses-two-operands` give the actual load operand list.
`p5-licm-guarded-instruction-reads-modeled-header`
identifies the result of the recognized load when the selected base is
bound and its header is readable.

The motion results use the scan's designated loop header and the
guarded-load equations use a represented heap. General motion
correctness also requires dominance, invariant operands, and preservation
of values across collection.

## Schedules with disjoint sources

`p6-disjoint-copies-are-emitted-in-order` proves the instruction order
when no pending destination is a source. The local lemmas
`p6-disjoint-copies-after-dropping-a-source`, `p6-tail-is-disjoint`,
`p6-disjoint-copies-need-no-self-copy-removal`,
`p6-disjoint-copy-list-needs-no-self-removal` and
`p6-disjoint-head-is-a-free-copy` establish the conditions for this
case. `p6-scheduling-step-on-disjoint-copies`,
`p6-scheduling-with-no-copies-gives-output`,
`p6-reversed-disjoint-copy-code`, `p6-double-reverse-onto` and
`p6-copy-order-is-a-list` give the scheduler and accumulator equations.

`p6-disjoint-copy-order-installs-snapshot` proves that executing the
listed instructions installs the bindings read from the original
environment. `p6-operand-is-the-same-in-qir-l-and-m` supplies the
common operand semantics. `p6-disjoint-schedule-installs-parallel-snapshot`
applies this result to the actual scheduler's output. These results
assume that evaluating the original operands succeeds.

## Value-stack slot clearing

`p6-clear-code-is-copy-and-stores` gives the execution order of
`abi-clears`. A nonempty selection begins with a copy of word 1 and
stores it in each selected slot. The local
`p6-clear-stores-are-generated-in-reverse`,
`p6-revappend-of-revappend` and `p6-clear-stores-are-a-list` give
the accumulator equations. `p6-clear-operand-is-word-one` gives the
value of the copied constant. `p6-clear-stores-write-only-selected-slots`
proves that the stores read that value and preserve every other slot.
`p6-emitted-clears-write-only-selected-slots` applies this result to the
actual clear sequence, assuming the selected slots belong to the frame.
`p6-state-transfer-matches-rewrite` equates the current and dirty sets
returned by the analysis transfer with those returned by the rewriter.
`p6-slot-difference-selects-unneeded-slots` characterizes the dirty
slots outside the needed set when both sets are in increasing order.
The local `p6-later-slot-is-larger` provides the order invariant.
`p6-clearing-stale-slots-preserves-needed-slot` applies the selection
result to the clear code and preserves each needed slot.

`p6-collector-forwarding-preserves-word-one` executes `rt:forward`
from the assembled runtime to return. The model places that routine at
address 0, uses return address 4096 and assumes that the instructions on
the relevant paths are installed. With at least nine steps and a word 1
in `x0`, every collection mode and source-range choice returns that word
with memory preserved.
`p6-cleared-slot-is-inert-under-forwarding` connects the actual QIR-L
clear sequence to that result when the slot datum is passed in `x0`.

The local `p6-forward-code-matches-at-each-address` and
`p6-forward-fetches-current-code` identify the words fetched from the
assembled routine. `p6-a64-unsigned-is-idempotent`,
`p6-state-fields-after-updates`, `p6-a64-flags-are-four-bits` and
`p6-general-register-read-ignores-use-sp` supply machine-state equations.
`p6-forward-exec-step-stays-on-immediate-path` proves that every step on
this path preserves memory and decreases the remaining step bound.
`p6-forward-path-observations` gives the register value and recognizes
the terminal bound. `p6-forward-run-on-immediate-path` lifts the step
result to execution with sufficient fuel.

The clear result assumes the needed set and the frame bounds. Proving
that every required root is available at every collection point also
requires the liveness, slot placement, and machine root-scanning invariants.

## Register assignment validation

`back-end-function` calls `rega-validated-program` on every MIR function. This
checks the homes, machine spill count and live-in sets returned by
`rega-allocation` before applying the assignment.
The check verifies that live-in sets satisfy the MIR transfers, parameters
have distinct homes, each live-through value survives the instruction's
clobbers and destination write, and each operand has a legal home. The
soundness theorems concern one instruction given agreement before its
clobbers, and the rewrite of its operands given agreement at their uses.
The check covers homes shared by coalesced temporaries in the original
MIR. Preservation over complete control-flow graphs and acceptance of
every valid MIR function remain proof obligations.

- `p8-validated-program-is-assigned-program` proves equality of the
  validated and ordinary allocator results when every assignment passes.
- `p8-rewriting-a-constant-preserves-value` and
  `p8-rewriting-live-operands-preserves-values` cover constant reads and
  lists of live operands under the assignment.
- `p8-pure-destination-is-temporary` and `p8-placed-destination`
  relate virtual destinations and their assigned homes.
- `p8-pure-rewrite-sources`, `p8-pure-rewrite-destination` and
  `p8-pure-rewrite-operation` describe the actual MIR rewrite on the
  pure instruction fragment.
- `p8-checked-pure-rewrite-preserves-agreement` combines the source
  reads, operation and destination write for that fragment. It uses the
  given agreement on live sources and on the values live through the
  instruction, together with the checked assignment.

Certification also executes examples of a loop with simultaneous phis,
word arithmetic at shift and overflow boundaries, heap loads, frame
slots, actual pass applications and A64 emission. The validator examples
accept actual allocations and reject a conflicting destination home,
incorrect liveness and homes clobbered by each kind of call.

On 2026-11-27, `sh compiler/bootstrap.sh` produced identical compiler
executables, `compiler-1` and `compiler-2`, with validation enabled.
