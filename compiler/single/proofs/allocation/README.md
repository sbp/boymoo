# Allocation, stack growth and publication

These ACL2 books connect the Linux AArch64 runtime to the allocator,
heap and value contracts in `compiler/single/proofs/foundations/interfaces.lisp`.
They take instruction operands and branch offsets from the assembled
runtime and Linux system wrappers. A checked instruction path requires
the expected decoded instruction and access permissions at every
visited address, with no early stop or requested cut. The corresponding
segment theorem uses the shared kernel and machine semantics.

## Stack growth and allocation

| Theorem | Statement |
| --- | --- |
| `allocation-growth-return-contract` | For an aligned request within a stack reservation ending at or below 2^63, both growth entries establish `proof-grow-return-p` and return to the caller. `rt:grow` may set X8 from X0 and `rt:ensure-stack` preserves X8. Both may change X9–X12, X24 and the flags. |
| `allocation-growth-checked-stop` | A request above the reservation establishes the stack resource bound and reaches `rt:stack-size`. |
| `allocation-linux-write-regions-bound-stack-reservation` | When the writable regions end at or below 2^63, the value-stack reservation has the same upper bound. |
| `allocation-fast-header-checked-contract` | `rt:alloc` returns the old header frontier, advances it by the request and leaves the cell frontier and heap limit fixed. It establishes the shared fast allocation contract. |
| `allocation-fast-cells-checked-contract` | `rt:alloc-cells` returns the lowered cell frontier, debits the heap limit by the same count and keeps the header frontier fixed. It establishes the shared fast allocation contract. |
| `allocation-fast-checked-return` | The fast paths reserve exactly the requested bytes and debit the shared budget. The header path may change X0, X1 and X27. The cell path may change X0, X1, X2, X9 and X26. Both may change the flags. The cell path writes the cell-frontier metadata word. |
| `allocation-header-overflow-edge` | Carry out of the 64-bit header sum establishes the word-size resource bound and reaches `rt:size`. |
| `allocation-slow-to-collector`, `allocation-slow-checked-return` | An insufficient budget passes the original byte count to `rt:collect`, with mode zero for headers and one for cells. Given the collector return contract, the tail call establishes the allocator return contract at the original link. |
| `allocation-collector-spills-request-and-mode`, `allocation-collector-request-size-checked-edge` | Collector entry saves the original request and mode. The entry guard rejects requests above a semispace before forwarding. |
| `allocation-collector-live-and-request-bound`, `allocation-collector-finish-checked-edge` | Ordered copy frontiers and a saved request bounded by a semispace make the finish comparison exact. It reaches `rt:heap-size` precisely when the sum of live and pending bytes exceeds a semispace. |

## Cons cells and publication

| Theorem | Statement |
| --- | --- |
| `allocation-cons-fast-checked-return` | The fast `CONS` path reserves a cell, stores the two operand words, and returns the tagged offset of the cell. |
| `allocation-cons-fast-checked-publication` | The fast path publishes the new cell and represents the Lisp pair of the two arguments. |
| `allocation-cons-fast-runtime-return` | The checked fast path establishes the shared `CONS` result, register and heap postcondition. |
| `allocation-cons-checked-to-growth`, `allocation-cons-checked-to-allocator` | The slow `CONS` path saves the frame and asks for two more stack words. After growth it installs both operands as value-stack roots and calls `rt:alloc-cells` for 16 bytes. |
| `allocation-cons-checked-prologue-to-roots`, `allocation-cons-prologue-memory-footprint` | The checked slow prefix reaches `rt:alloc-cells` with the caller's saved frame and both operand words in the root slots. Its only writes are the two saves and the two root words. |
| `allocation-cons-prologue-roots-represent-arguments` | The four writes in the slow prefix preserve the old object views, so the two stored roots represent the original arguments. |
| `allocation-cons-prologue-preserves-shared-heap-frame`, `allocation-cons-prologue-preserves-live-stack`, `allocation-cons-prologue-preserves-dynamic-table` | The prefix preserves the caller's heap frame, the live stack below its two new roots, and the dynamic table. |
| `allocation-cons-growth-premises-from-linux-layout`, `allocation-stack-prefix-extended-with-argument-pair` | The saves leave the growth bounds intact. An aligned live stack with two represented argument words extends to a valid prefix containing the two argument views. |
| `allocation-cons-checked-allocator-entry-has-heap` | The decoded slow prefix establishes a valid heap at `rt:alloc-cells` with a 16-byte request and the two represented arguments appended to the live value stack. |
| `allocation-cons-two-roots-after-allocator`, `allocation-cons-checked-publication-after-allocator` | Given the allocator contract, both reloaded roots retain their source values. The continuation initializes and publishes the pair, returns its represented value, pops both roots and restores the saved frame and link. |
| `allocation-cons-checked-heap-continuation` | The same continuation establishes the heap predicate with the published pair and preserves the original stack prefix and dynamic table after removing the two temporary roots. |
| `allocation-cons-checked-runtime-return-from-roots` | Given an executed prefix that sets up the saved frame and both roots and reaches the allocator return, the checked continuation establishes the shared `CONS` runtime return predicate at the original call. |
| `allocation-cons-checked-runtime-return-through-allocator` | The decoded slow prefix establishes the caller's frame and both argument roots. With an executed allocator segment satisfying its shared return contract, the decoded continuation establishes the shared runtime return predicate at the original call. |
| `allocation-view-after-disjoint-write`, `allocation-object-map-after-disjoint-write` | A write disjoint from published object spans preserves the views and validity of the existing map. |
| `allocation-heap-after-unpublished-active-word-store` | A word store in the active semispace that avoids the published objects preserves the heap with its existing object map. |
| `allocation-publish-initialized-cons`, `allocation-initialize-and-publish-cell` | Given the fresh span, the new cell's two field values and a sufficient rank for the children, initialization and publication admit a record for the corresponding Lisp pair. |
| `allocation-published-cons-admits-heap` | Adding an already valid cons record in the allocated cell interval to a heap preserves the shared heap predicate. |
| `allocation-publish-initialized-external-string` | An initialized external header and its padded span admit a record whose value is the string read from the payload. |
| `allocation-published-objects-avoid-fresh-or-stack-span` | A span outside the heap reservation and either disjoint from all existing regions or contained in a stack reservation is disjoint from all published objects. |
| `allocation-stack-write-state-keeps-heap-with-new-stack-prefix` | Word writes confined to the stack reservations keep the heap valid when the new stack pointers stay in their reservations and the new live prefix has valid views. |
| `allocation-stack-write-state-keeps-existing-heap` | Stack writes that avoid the caller's live value and machine stack ranges preserve the existing heap contract at an unchanged value-stack top. |
| `allocation-step-preserves-word-address-keys`, `allocation-executed-prefix-preserves-word-address-keys`, `allocation-checked-path-preserves-word-address-keys` | An initial sparse memory whose keys are unsigned 64-bit addresses retains that property through the Linux instruction and system-call model, a finite executed prefix, or a checked instruction path. |
| `allocation-linux-loader-keeps-word-address-keys` | A Linux image load preserves valid sparse address keys from the supplied processor memory. |

## Large strings

| Theorem | Statement |
| --- | --- |
| `allocation-large-size-checked-edge`, `allocation-large-rounding-machine-edge` | Lengths of 2^32 bytes or more reach `rt:datum-size`. For smaller lengths the rounding instructions compute the 64 KiB ceiling of the length plus 32 bytes. |
| `allocation-large-budget-machine-edge`, `allocation-large-collection-continuation` | A nonzero counter and an over-budget sum select a zero-byte header collection. With the collector contract, the continuation retains the length and rounded size and reaches `rt:map-string`. |
| `allocation-map-success-checked-svc`, `allocation-map-refusal-checked-svc` | An admitted Linux mapping reply appends a cleared writable interval. A Linux error reply is recognized as a refusal, with memory and regions preserved. Both consume the reply. |
| `allocation-map-checked-tail-return`, `allocation-large-refused-request-exits` | The mapping wrapper converts a negative reply to zero. A zero result reaches `rt:memory` and yields the status-3 resource observation under the stop contract. |
| `allocation-large-checked-return-from-map-call` | The decoded call from `rt:map-string` returns to the constructor with a cleared writable region on success or zero on refusal. It consumes the reply and preserves the caller's saved-register frame. |
| `allocation-large-checked-map-refusal-exits`, `allocation-large-unrepresentable-request-exits` | A refused mapping reaches `rt:memory`, and a length of 2^32 bytes or more reaches `rt:datum-size`. Each yields the status-3 resource observation under the stop-handler contract. |
| `allocation-large-successful-map-keeps-old-heap` | When every stored byte belongs to a readable region, mapping a fresh region leaves the sparse memory of the old heap unchanged. The old heap is valid with the appended region. |
| `allocation-large-postmap-checked-return`, `allocation-large-initialization-preserves-bookkeeping` | The 17-instruction continuation links the new mapping, adds its size to the counter, installs the string header, returns the payload address and tagged datum, and restores the saved registers. The mapping mark and budget are preserved. |
| `allocation-large-initialized-payload-stays-zero`, `allocation-large-publishes-external-list`, `allocation-large-result-after-publication` | A cleared mapping retains zero payload bytes. The initialized mapping can be prepended to the external list, and a fresh header can be added to the published map to establish `proof-string-result-p`. The publication theorems specify the required surviving list and object-map invariants. |
| `allocation-large-checked-initialization-and-publication` | At a successful mapping return, the checked continuation preserves the old map from the disjointness of its five writes and publishes the represented string. |
| `allocation-large-keeps-old-external-list`, `allocation-large-accounting-after-publication` | With unchanged mapping bounds and disjoint writes, the old list and its mapped-byte total are preserved. Adding the new size and counter preserves string accounting when the total is below 2^63. |
| `allocation-large-checked-heap-return-from-mapping` | Starting at a successful cleared mapping with a valid old heap, the checked continuation establishes the shared heap-preservation and string-result predicates with the new external record. |
| `allocation-large-size-prefix-saves-caller` | The constructor entry saves X19–X21 and the caller's link and keeps the requested length in X19. |
| `allocation-large-checked-entry-to-budget` | The checked entry reaches the budget test with the caller's saved frame, the rounded mapping size, the metadata address, and the counter and budget words read from the heap. |
| `allocation-large-checked-entry-preserves-heap-to-budget`, `allocation-large-checked-budget-branches-with-heap-and-saves` | The entry saves fit below the live machine stack. The checked entry and budget branches preserve the heap and leave the caller's save record in place, including at the collector call. |
| `allocation-large-budget-check-preserves-caller-saves`, `allocation-large-collector-return-preserves-caller-saves` | The budget instructions and a collector return satisfying its shared contract preserve the constructor's four saved words and its register frame. |
| `allocation-large-constructor-checked-return-from-mapped-state` | Given an executed prefix and a successful mapping with the saved caller state, the checked continuation establishes the shared string-constructor return predicate at the original call. |
| `allocation-large-constructor-checked-return-through-map` | Given an executed prefix to `rt:map-string` preserving the caller's heap and saved frame, the checked mapping and publication paths establish the string-constructor return predicate at the original call. |
| `allocation-regions-total-fits-range`, `allocation-adding-fresh-region-bounds-external-byte-total` | Disjoint regions occupy at most the size of their containing interval. A finite external list names distinct registered regions. If the writable regions satisfy the Linux address bound, adding a fresh mapping keeps the total below 2^63. |
| `allocation-linux-loader-keeps-writable-region-bounds`, `allocation-linux-writable-regions-preserved-by-step`, `allocation-linux-writable-regions-preserved-by-prefix` | A Linux image load preserves the writable-region address bound of the supplied regions. The model preserves the bound through instruction execution, system calls and finite execution prefixes. |
| `allocation-large-mapped-total-fits-linux-range` | When the writable regions satisfy the Linux address bound, the old external byte total plus the successful new mapping size is below 2^63. |
| `allocation-large-checked-entry-to-map`, `allocation-large-constructor-checked-return-from-entry` | The decoded entry and budget branch establish the mapping call's heap, frame and argument conditions. For the collection branch, the executed collector prefix and its return contract supply the next state. With an admitted mapping, the caller's Linux writable-region bound supplies the accounting bound and the checked continuation establishes the shared constructor return. |
| `allocation-large-constructor-checked-refusal-from-entry` | Starting at the constructor call, either budget branch followed by a refused mapping reaches `rt:memory` and yields the status-3 resource observation under the collector and stop-handler contracts. |

## Boundaries

`allocation-growth-overflow-example` executes the decoded stack-growth
path with a reservation at the top of the 64-bit address range, where
doubling wraps and the runtime selects a smaller limit than
`proof-grow-limit`. `proof-heap-layout-p` excludes that layout: it
requires the stack base plus twice the reservation to be at most 2^64.
An admitted Linux stack reservation ending at or below 2^63 supplies the
bound used by the return theorem.

`allocation-collector-count-overflow-example` executes the finish
comparison with a saved request outside the entry guard. The mathematical
sum exceeds a semispace, but the wrapped sum reaches the fall-through.
The finish theorem uses the saved-request bound. Preservation of that
bound through the collector body is a collector obligation.

The instruction placement and access premises, the collector return
predicate and the resource-handler exit segment are explicit contracts.
The slow `CONS` return uses the Linux bound on the value-stack
reservation, room for the saves and roots, and an executed allocator
segment satisfying its return contract.
The caller frame proofs use unsigned 64-bit memory keys to compose
sparse memory agreement. The entry proofs derive this property for
their intermediate and returned states. The mapping composition uses
the premise that existing sparse memory entries lie in readable regions.
The large string accounting proof derives the bound on the sum of the
mapped bytes from the Linux writable regions. The loader takes the
initial regions as input, so the writable-region bound starts as a
condition on those regions. Deriving sparse memory coverage from the
loader and maintaining it through the collector remain open.

## Certification

Run the following from the repository root with ACL2 8.7 on the
command path and the arithmetic and bit-operations community books
available through the ACL2 system book directory.

```sh
SBCL_USER_ARGS='--dynamic-space-size 2500' sh compiler/single/proofs/certify.sh --foundations
sh compiler/single/proofs/allocation/certify.sh
```

On 2026-11-26 the foundations command certified 21 books and printed
`Compiler proof foundations certified.` It took 27 seconds.

On the same date the allocation command certified all 61 books in
logic mode with ACL2 8.7. Both boundary assertions printed `:PASSED`.
The command took 597 seconds while five other packages were certified
beside it. The certificates and transcripts
are under `build/compiler/single/proofs/`.
