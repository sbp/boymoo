# Sequences and coercion

These ACL2 books concern the Linux A64 instructions emitted for
`runtime-sequence-code` and the values of `COERCE`, `LENGTH`, `CHAR`,
and `SUBSEQ` in the source model. A cons spine is the finite chain of
conses reached through successive cdr fields. Its length counts the
conses, including when the last cdr is an atom other than NIL.

An instruction path is a list of instructions decoded from the
assembled Linux system and runtime items. The predicate
`sequence-instruction-path` requires each instruction at the current
program counter with its checked memory access permitted. It also
requires execution to remain outside the named cutpoints before each
step. `sequence-segment-of-instruction-path` converts these premises
and the final cutpoint test into a finite `proof-segment-p` result.

## Source values and helper routines

| Book and theorem | Statement |
| --- | --- |
| `source`, `sequence-core-coerce` | The symbol COMMON-LISP::LIST selects the character list of a string or NIL. Every other result type selects a string formed from the cons spine, with a zero byte for each noncharacter element. |
| `source`, `sequence-core-length` | The source result is the byte length of a string or the length of a cons spine. |
| `source`, `sequence-core-char` | On input with the stated length bound, the runtime count selects the source character, with NIL for a non-string or a position outside the string. An index that is not a positive integer counts as zero. |
| `source`, `sequence-core-subseq` | On input with the stated length bound, the source result is a slice with a fixed start, a size computed using the original start in subtraction, and a default end equal to the sequence length. The list slice pads with NIL, and string coercion turns the padding into zero bytes. |
| `source`, `sequence-runtime-count-for-lookup` and `sequence-runtime-count-exact-for-bounded-size` | Saturating a positive boxed count at 2^32 preserves the lookup test against a length at most 2^32. A count below the size check equals the exact fixed count. |
| `views`, `sequence-cons-fields-of-represented-value` and `sequence-string-view-of-represented-value` | The value view relates a cons to its two stored words and a string to its header and payload. |
| `view-memory`, `sequence-view-of-equal-memory` and `sequence-fresh-object-preserves-old-value-view` | With memory and the interpretation of object addresses fixed, changes to other machine fields preserve a datum's view. Prepending a record at a fresh address also preserves old value views on that memory. |
| `helpers`, `sequence-string-view-field-contract` | The checked helper returns the payload address and byte length of a represented string in X1 and X2, or two zero registers for another datum. It preserves the registers outside X1 through X3 and restores SP and the caller's program counter. |
| `length`, `sequence-list-length-contract` | The checked helper visits the cells of the input cons spine, returns its length in X2 with the original datum still in X0, and preserves memory. `sequence-list-length-step-count` gives its count of five instructions plus six per cell. |
| `counts`, `sequence-index-count-contract` | The checked helper returns the positive immediate count, the saturated positive boxed count, or zero. The boxed classification uses the integer header and its sign field. |
| `heap-bounds`, `sequence-represented-string-length-bounded` | Every represented string is shorter than 2^32 bytes. The proof uses the static, active, and external object spans. |
| `spine-bounds`, `sequence-cons-spine-of-represented-datum` and `sequence-represented-sequence-length-bounded` | The heap invariant supplies the cons-spine predicate, and the source sequence length is below 2^32. Cons views descend in rank and there are at most 2^31 distinct aligned cons addresses in the bounded heap span. |
| `spine-bounds`, `sequence-list-length-for-represented-datum` | From a represented datum in the shared heap invariant, the checked list-length helper returns the number of conses and preserves memory and the register frame. |

## Construction and copying

| Book and theorem | Statement |
| --- | --- |
| `constructors`, `sequence-small-string-allocation-request` | For a byte length below 2^18, the code saves the input length and link in a 16-byte frame and calls the header allocator with the rounded byte count. |
| `constructors`, `sequence-empty-string-tail-call` and `sequence-large-string-tail-call` | The empty constructor tail calls the string constructor with length zero. A length at least 2^18 takes the large-string tail call. |
| `constructors`, `sequence-small-string-initialized-storage` | At the small constructor's allocator continuation, the code initializes the header and zeroes past the payload through the end of the allocation. It returns the writable payload address in X1 and byte length in X2. `sequence-small-string-write-extents` gives the exact spans and `sequence-small-string-finish-effects` gives the tagged result word. |
| `constructors`, `sequence-small-string-finish-contract` | The checked suffix returns a writable string of the requested length. Its tagged word decodes using the object map extended with the new header. |
| `constructors`, `sequence-allocator-keeps-small-string-saves` | The allocator return contract preserves the two saved words when their frame span fits in the preserved machine stack. |
| `constructor-calls`, `sequence-small-string-call-to-allocator` and `sequence-empty-string-call-to-constructor` | The checked entry segments reach the allocator with the computed size and two saved words, or reach the string constructor with length zero and the original link. |
| `constructor-calls`, `sequence-small-string-after-allocator` | From the shared allocator return contract and the saved machine frame, the checked continuation returns a writable string of the requested length. The reserved heap span supplies the alignment, address range, and write coverage. |
| `constructor-storage`, `sequence-small-constructor-init-is-an-active-write` | On word-addressed memory, the small constructor's header and padding stores are confined to its active-space reservation. The theorem supplies the heap-register and stack conditions used by `active-frame`. |
| `roots`, `sequence-root-reload-effects` and `sequence-reloading-preserved-root` | The emitted reload sequences pop the appropriate slots and recover the original value view when allocation or arithmetic preserves the root views. The loaded word may have a different address. |
| `subseq-counts`, `sequence-subseq-immediate-count-segment` and `sequence-subseq-arithmetic-result` | With immediate start and effective end, the checked instructions produce the fixed start count and the positive part of the unfixed difference. The two primitive source results in the general case compose to that same unfixed difference. |
| `copy-loops`, `sequence-coerce-list-step-effects` and `sequence-coerce-string-step-effects` | A string-to-list iteration reads a byte in reverse order and writes one cons with the previous result as its cdr. A list-to-string iteration reads one cons and writes the encoded character or a zero byte. |
| `copy-loops`, `sequence-subseq-drop-cell-effects` and `sequence-subseq-list-step-effects` | A list drop advances through one cdr. A list result iteration writes one cons with the next element or NIL and uses NIL as the final cdr. |
| `list-drop`, `sequence-subseq-list-drop-segment` | The checked drop reaches the allocation cutpoint with the tail represented in X0. Taking the requested number of elements from that tail gives the same slice as the source even for a saturated start count. |
| `coerce-copy`, `sequence-coerce-input-cells-from-view` and `sequence-coerce-string-copy-source-value` | With disjoint input cells and output bytes, the checked list-to-string copy writes the completed character code of each input element. Reading that buffer gives the source result for any result type other than COMMON-LISP::LIST. |
| `string-copy`, `sequence-subseq-string-copy-segment` and `sequence-subseq-string-copy-source-value` | From a prepared loop entry, the checked copy runs to completion. Each output byte is the corresponding source byte or zero beyond the source end. Reading the destination for the requested length gives the source result. |
| `string-results`, `sequence-coerce-string-copy-returns-represented-value` and `sequence-subseq-string-copy-retains-represented-value` | With a represented header for the output buffer at loop entry, the writes preserve that header. The result word in X0 for `COERCE` or X6 for `SUBSEQ` decodes to the source string at the loop exit. |
| `copy-returns`, `sequence-coerce-copy-returns-represented-result` and `sequence-subseq-copy-returns-represented-result` | The checked exits of the string and cons copy loops reach the saved return address, reload the saved registers and SP, and carry the represented result into X0. |
| `cons-records`, `sequence-ranked-records-for-backward-copy` and `sequence-ranked-records-for-forward-copy` | Explicit extensions of the object map satisfy the rank checks for cells written in both directions. |
| `copy-loops`, `sequence-byte-iteration-extent`, `sequence-cons-iteration-extent`, `sequence-forward-iteration-progress`, and `sequence-backward-iteration-progress` | A valid iteration stays within the supplied byte or cell span, and the number of iterations remaining decreases. |
| `copy-loops`, `sequence-subseq-size-cutpoint` and `counts`, `sequence-subseq-result-size-limit` | At a count of 2^32 or greater, the checked path reaches `rt:datum-size` and the real string length or cons allocation meets the corresponding resource predicate. |
| `resources`, `sequence-subseq-size-stop-with-handler` | The checked size rejection composes with a status 3 exit-handler segment satisfying the shared resource observation. |
| `returns`, `sequence-length-checked-return` and `sequence-char-checked-return` | Given the length or the indexed string payload at the return continuation, the checked instructions represent the source result. The non-string `CHAR` path returns the NIL word, and the raw return lemmas give the restored stack and link. |
| `view-calls`, `sequence-view-call-cutpoint`, `sequence-length-dispatch-cutpoint`, and `sequence-char-index-cutpoint` | The checked entry and dispatch instructions install the arguments and link for the view and count helpers, and send `LENGTH` to list length or result tagging. |
| `length-resume`, `sequence-length-from-view-to-source` | The checked continuation of `LENGTH` from the string-view return counts a cons spine when needed, tags the source length, and reaches the saved return address. |
| `char-resume`, `sequence-char-from-view-to-source` | The checked continuation of `CHAR` from the string-view return fixes the index on the string path and returns the source character or NIL at the saved return address. |

## Public calls and the heap

| Book and theorem | Statement |
| --- | --- |
| `stack-invariant`, `sequence-confined-stack-write-preserves-heap` and `sequence-confined-stack-write-preserves-value` | A checked machine-stack frame below the caller's SP preserves the shared heap invariant, the fixed heap, and the meaning of every represented value. |
| `static-roots`, `sequence-static-truth-values-in-heap` | The static NIL and T words have their source values in the full heap object map. |
| `register-only`, `sequence-register-only-change-keeps-heap` | A change that leaves the heap registers, SP, memory, and the world fields outside the machine unchanged preserves the current heap and its views. |
| `length-entry`, `sequence-length-runtime-contract` | From the shared runtime precondition and a checked path with room for the machine-stack frame, `LENGTH` reaches its original return address with the shared return contract and the same object map. |
| `char-entry`, `sequence-char-runtime-contract` | Under the same entry conditions, `CHAR` reaches its original return address and satisfies the shared return contract for character and NIL results. |
| `coerce-type`, `sequence-coerce-type-test-agrees-with-source` and `sequence-coerce-dispatch-for-represented-type` | The runtime's tag, header, package number, name length, and packed name tests identify the represented symbol COMMON-LISP::LIST. The checked instructions reach the corresponding list or string branch with their register and memory effects. |
| `coerce-empty-list`, `sequence-coerce-empty-list-runtime-contract` | A checked call with result type COMMON-LISP::LIST returns NIL for a non-string or an empty string. It satisfies the shared runtime contract and preserves the fixed heap. |
| `coerce-atom-string`, `sequence-coerce-atom-string-runtime-contract` | A checked call with a non-cons input and a result type other than COMMON-LISP::LIST tail calls the empty-string constructor. Its shared return contract follows from the constructor's checked return segment and shared constructor contract. |
| `coerce-atom-string`, `sequence-coerce-atom-string-from-header-allocator` | The atom-to-string call composes with the checked empty constructor through its imported header allocator return and heap publication condition. |
| `coerce-list`, `sequence-coerce-list-copy-segment` and `sequence-coerce-list-copy-effects` | The backward byte copy completes in eight instructions per byte, writes one cons per byte, and leaves the head word in X0. |
| `coerce-list-layout`, `sequence-coerce-list-cell-contents` | Every cell in the reservation has the correct character word and cdr. The first cell written receives the supplied tail, and each later cell links to its predecessor in memory. |
| `coerce-list-view`, `sequence-coerce-list-copy-source-value` | The head word after the checked backward copy represents the source character list in a map containing the specified ranked cons records and NIL. The input bytes and output cells occupy disjoint spans. |
| `coerce-list-resume`, `sequence-coerce-list-ready-from-allocator` | After the shared cons allocator return, the checked continuation reloads the string from its live root, obtains the view at its current address, and enters the backward loop with the allocation cursor, byte count, and NIL tail. |
| `coerce-string-resume`, `sequence-coerce-string-ready-from-constructor` | After the shared string constructor return, the checked continuation pops and reloads the movable list root into X4, preserving the writable string result in X0 through X2. |
| `coerce-allocation`, `sequence-coerce-copy-requests-root-space` and `sequence-coerce-requests-construction-after-growth` | At a positive count, the checked copy preparation requests one root slot. After the shared growth return it saves the source word and passes the cons byte count or string length to the corresponding constructor. |
| `subseq-list-fill`, `sequence-subseq-list-fill-effects` and `sequence-subseq-list-fill-segment` | The forward copy completes from its prepared entry, writes within its reservation, pads an exhausted cons spine with NIL, and sets the last cdr to NIL. |
| `subseq-list-layout`, `sequence-subseq-result-cell-contents` | The car of each initialized cell is the stored word selected from the input or the NIL word. Its cdr is the next cell's pointer or NIL at the last cell. |
| `subseq-source-words`, `sequence-subseq-selected-words-represent-take` | The selected words represent the first requested number of elements with NIL padding in an extended map whose old storage and records agree. |
| `subseq-list-view`, `sequence-subseq-list-fill-source-value` | The checked forward copy from a represented tail builds a word for the source take with NIL padding. The result map contains the specified ranked cons records and agrees with the old map and storage. |
| `subseq-view`, `sequence-subseq-view-call-effects`, `sequence-subseq-end-branch-effects`, and `sequence-subseq-default-end-tags-length` | The prologue saves the caller's registers and passes the sequence to the view helper. The next instructions select the explicit end or the length, distinguish strings from other data, and tag the default length. |
| `subseq-entry`, `sequence-subseq-entry-to-effective-end` | From the shared public precondition, the checked path establishes represented registers for the sequence, start, and effective end, with the string flag and the reserved caller frame. NIL end uses the sequence length. |
| `subseq-select`, `sequence-subseq-bounded-selection` | The checked size test below the cutoff reaches the string branch, nonempty list branch, or NIL branch with the exact source result size. |
| `subseq-empty-list`, `sequence-subseq-empty-list-after-size-check` | For a zero-size non-string result, the checked path returns NIL and reloads the caller's registers from the saved frame. |
| `subseq-immediate-frame`, `sequence-subseq-counts-from-represented-immediates` | For represented immediate integers at the effective-end cutpoint, the checked instructions reach the size test with the exact source size and fixed start, with memory and the saved machine frame preserved. |
| `subseq-empty-entry`, `sequence-subseq-empty-list-immediate-runtime-contract` | For a non-string input, immediate start and effective end, and zero source result size, the checked public call returns NIL with the original frame, object map, and fixed heap. |
| `canonical-symbols`, `sequence-nil-word-is-canonical` | The NIL test compares against the unique stored word for NIL in the shared heap, using uniqueness of represented symbols in the object map. |
| `root-prefix`, `sequence-runtime-return-preserves-root-slot` | A shared runtime return preserves the value represented in a selected slot of its caller's live root prefix. |
| `root-storage`, `sequence-pushed-root-views` and `sequence-popped-root-views` | Adding represented slots immediately above the current top extends the stack view and preserves the old prefix. Popping aligned slots with memory unchanged preserves the prefix below the new top. |
| `publication-views`, `sequence-old-view-after-publication` | A valid old view is unchanged when its object's storage and address lookup agree in the extended map. |
| `publication-map`, `sequence-object-map-after-publication` | A run of initialized, well-formed active nonsymbol records at fresh, disjoint addresses extends the object map and preserves the static records. The same book preserves old stack views and external mapping lists under agreeing lookups. |
| `publication-memory`, `sequence-disjoint-reservation-preserves-object-storage` and `sequence-reservation-contains-no-published-address` | Stores confined to a reserved interval preserve storage for disjoint old objects, and the interval contains none of their published addresses. |
| `active-frame`, `sequence-active-write-keeps-heap-metadata`, `sequence-active-write-keeps-heap-layout`, and `sequence-active-write-keeps-caller-heap-frame` | Stores confined to the active space, with unchanged heap registers and SP in its allowed range, preserve the heap metadata, dynamic root word, physical layout, and the caller's heap frame. |
| `publication-heap`, `sequence-publish-active-nonsymbol-objects` | Initialized, ranked, disjoint nonsymbol records establish the shared preserved heap in the extended map when the physical layout, heap frame, old storage, static map, external traversal, and dynamic root are preserved. |
| `publication-string`, `sequence-publish-initialized-string-in-reservation` | An initialized string header at a reserved address provides the fresh rank-zero record and its active-heap placement. Under storage preservation, the extended map satisfies the shared preserved heap. |
| `publication-string`, `sequence-small-string-finishes-and-publishes` | The checked small constructor continuation initializes the header and produces the shared writable string result. With the storage preservation premises, it also establishes the shared preserved heap in the extended map. |
| `heap-compose`, `sequence-word-addressed-heap-frames-compose` and `sequence-word-addressed-preserved-heaps-compose` | Heap frames compose when the endpoint memories have word addresses and the intermediate frame covers the original caller's stack span. Non-interning heap preservation also composes when the intermediate value-stack top equals the original top. |
| `subseq-arithmetic`, `sequence-subseq-arithmetic-growth-call`, `sequence-subseq-arithmetic-start-count-call`, and `sequence-subseq-arithmetic-negation-call` | The general count path requests room for the two roots, stores the source and effective end, and reaches the count and negation calls with the corresponding arguments. |
| `subseq-root-push`, `sequence-subseq-numeric-pushes-represented-roots` | From the checked post-growth state with room and disjoint storage, the emitted push extends the value stack with represented source and effective-end slots and preserves the old prefix. |
| `subseq-start-call`, `sequence-subseq-negation-precondition` | With the two required live root slots, the checked start-count return establishes the shared negation precondition. |
| `subseq-call-contracts`, `sequence-subseq-addition-precondition` | After the imported negation return, the checked instructions reload the effective end from its live slot and establish the shared addition precondition. X20 retains the fixed start count. |
| `subseq-call-contracts`, `sequence-subseq-size-from-addition-return` | After the imported addition return, the checked count and reload reach the size test with the difference count in X19 and the represented sequence in X0. The count equals the exact source size below the cutoff. |
| `subseq-numeric-run`, `sequence-subseq-numeric-through-both-arithmetic-calls` | From the negation call with two live source roots, the checked path composes the imported negation and addition returns and reaches the size test. The addition precondition, bounded result size, fixed start count, and reloaded source value hold. |
| `constructor-entry`, `sequence-small-string-from-entry` and `sequence-empty-string-from-entry` | From the constructor entry, the checked path and imported allocator return reach the original return address with the initialized, writable string result and its object record. |
| `constructor-entry`, `sequence-small-string-restores-call-frame`, `sequence-small-string-constructor-with-publication`, and `sequence-empty-string-constructor-with-publication` | The small constructor restores the caller's machine frame. Supplying the shared heap publication condition yields the full shared return contract for the small and empty constructors. |
| `datum-stop`, `sequence-datum-size-handler-completes` and `sequence-oversized-subseq-exits` | The checked size rejection establishes the resource predicate for the requested result. The diagnostic and newline are passed to the write routine on descriptor 2, and the handler reaches Linux exit status 3 with empty standard output under the two write return contracts. |
| `subseq-size-entry`, `sequence-subseq-immediate-size-exhaustion` | From the public entry with immediate start and effective end, an exact result size at or above the cutoff takes the checked size rejection and reaches status 3 with empty standard output under the two write return contracts. |

The books `words`, `state`, `instructions`, `shifts`, and `memory`
give supporting arithmetic, A64 state and instruction effects, and
checked-span lemmas. In particular, `sequence-read-after-own-write`
and `sequence-read-outside-write` establish the values read after a
store, and `sequence-agreement-preserves-load` uses the shared memory
agreement predicate to protect a load wholly inside an agreed span.

The book `span-composition` supplies a counterexample and a restricted
composition theorem. In `sequence-span-agreement-can-fail-to-compose`,
the memories with the single entry `(3/2 . 0)`, no entries, and the
single entry `(0 . 1)` agree in adjacent pairs on the interval
`[1, 2)` under `proof-memory-span-agrees-p`. The first and last fail
to agree because the byte reader interprets the fractional key as
address zero. In `sequence-word-addressed-span-agreement-composes`, the
endpoint memories have unsigned 64-bit integer keys, and agreement
composes on natural-number intervals. The theorem
`sequence-a64-writes-keep-word-addresses` shows that the A64 byte
store preserves this memory invariant.

## Open obligations

The checked path predicates take code placement and permitted accesses as
premises. The `LENGTH` and `CHAR` entry theorems require room for the
16-byte machine-stack save. The `SUBSEQ` prologue uses a 32-byte save.
The frame preservation proofs place these saves above address zero.
Resource proofs for exhausting machine-stack space remain open.

Entry-to-return proofs for the allocating copy cases of `COERCE` and
`SUBSEQ` remain open. The storage, map, and publication lemmas apply
to initialized records in a reservation. The emitted instructions
must connect their stores and live root updates to those premises
at each call site. The publication proof also requires preservation
of the static map, external mappings, and string accounting. The
caller's heap frame must compose across the allocating calls. The
small constructor uses the resulting publication condition in its
shared `proof-string-constructor-return-p`.

A shared publication rule could derive static map validity and
preservation of the external mapping traversal and accounting
from an allocator's reserved span and stores confined to that
span. The result map and its ranked records would then discharge
the physical storage premise at each call.

The general `SUBSEQ` count proof uses the imported `UNARY--` and
`BINARY-+` contracts. Composition with the entry and growth stages
must connect the two slots from the checked push to the negation
call. The push theorem takes represented source and end registers
after growth and disjointness from old objects as premises.
Growth, allocation, and large-string calls still need their imported
success and resource cases at the sequence call sites. The checked
size rejection uses the two diagnostic write returns. A shared
`rt:write-all` contract for descriptor 2 would supply finite
return to X30, preserving X22, standard output, and the machine
frame for the diagnostic buffer and newline.

The shared growth return would supply the needed source and end
representations if it required equal value views for each of X0
through X7 in the old and new maps. A shared root update lemma could
derive disjoint storage and heap preservation from the value-stack
reservation, the old heap layout, and the represented slots.

A shared memory invariant requiring unsigned 64-bit integer keys in
the machine state would allow span agreement to compose across
allocator and runtime returns using the restricted theorem. A
foundation definition of byte-entry agreement restricted to those
keys would also remove the fractional-key case.

## Certification

Run both commands from the repository root.

```sh
SBCL_USER_ARGS='--dynamic-space-size 2500' sh compiler/single/proofs/certify.sh --foundations
sh compiler/single/proofs/sequences/certify.sh
```

On 2026-11-26, ACL2 8.7 certified the 21 compiler, model, and foundation
books and all 92 books in this package. Both commands exited with status
zero.

| Command | Last certification line | Elapsed time |
| --- | --- | ---: |
| Foundations | `Compiler proof foundations certified.` | 27 s |
| Package, beside five other packages | `Certified compiler/single/proofs/sequences/constructor-storage.lisp.` | 742 s |
