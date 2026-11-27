# Copying collection

These books concern the copying collector in `compiler/single/runtime.lisp`.
The collector visits the dynamic symbol table and the initialized
value stack, then scans objects copied to the two ends of the
destination semispace. A semispace is one of the two reserved heap
intervals used alternately for collection. The collector keeps
separately mapped strings at their addresses and marks them for the
string sweep. The proof interface for the whole routine is
`proof-collector-return-p`.

## Certification

Run these commands from the repository root with ACL2 8.7 and its
system books available.

```sh
SBCL_USER_ARGS='--dynamic-space-size 2500' sh compiler/single/proofs/certify.sh --foundations
sh compiler/single/proofs/collection/certify.sh
```

On 2026-11-26 the first command printed
`Compiler proof foundations certified.` in 27 seconds. The second
command printed `Certified compiler/single/proofs/collection/BOOK.lisp.` for
each of the 76 books, ending with `examples.lisp`, in 622 seconds
while five other packages were certified beside it.
The command `rg -c '^:PASSED$' build/compiler/single/proofs/collection/examples.out`
printed `8` on the same date.
The command
`SBCL_USER_ARGS='--dynamic-space-size 2500' sh compiler/single/proofs/certify.sh --books collection sweep-geometry`
printed `Certified compiler/single/proofs/collection/sweep-geometry.lisp.`
on the same date in 2.85 seconds with a peak child resident set of
538,378,240 bytes.
These runs check the theorems and examples below in logic mode.
The certificates and logs are under `build/compiler/single/proofs/`.

## Forwarding and copying

`machine.lisp` defines an instruction trace as addresses paired with
decoded instructions. `collection-ready-trace-reaches-cut` identifies
its instruction effects with `proof-segment-p`. Readiness requires
placement and permitted accesses at each step, and requires that the
trace reaches the cutpoint for the first time at its end.
`words.lisp`, `actions.lisp`, `comparisons.lisp` and `memory.lisp` supply
word arithmetic, instruction effects and byte-memory facts for these
traces. In particular, `collection-unsigned-comparisons` interprets the
condition flags after subtraction, `collection-read-of-same-word`
recovers a stored word, and
`collection-disjoint-word-store-preserves-word` preserves a read
outside the store.

`segments.lisp` composes checked prefixes. A prefix excludes its
cutpoints until its last instruction has executed.
`collection-ready-trace-gives-prefix` identifies the prefix state
with the trace effect, and `collection-prefix-append` composes two
prefixes. `placement.lisp` proves that an instruction's bytes survive
writes to writable regions. `regions.lisp` proves that unmapping
preserves coverage of disjoint spans.

`forward.lisp` assembles and decodes the compiler's `rt:forward`
instructions. A tag is the low three bits of a datum word. A
forwarding entry associates an original address with its assigned
destination. At a moved source, the collector records the new datum
word with a marker identifying the entry. The theorems describe the
following cutpoints.

| Theorem | Statement |
| --- | --- |
| `collection-forward-immediate-selects-return` | An immediate selects the return instruction with its word and memory unchanged. |
| `collection-forward-decodes-pointer-address` | The tagged word becomes the address given by `proof-pointer-address` and selects the header or cons path. |
| `collection-forward-tests-cons-region` | A cons address below the old-space floor selects the unchanged return. |
| `collection-forward-tests-header-region`, `collection-forward-tests-low-header-region`, `collection-forward-tests-high-header-region` | Header comparisons select the branches for a static header, a movable header or a separately mapped string. |
| `collection-forward-tests-cons-marker`, `collection-forward-tests-header-marker` | The cons tag or header high bit selects the reuse branch. |
| `collection-forward-seen-cons-effect`, `collection-forward-seen-header-effect` | Reuse returns the saved cons word or the saved header word with its marker bit cleared. |
| `collection-forward-copy-cons-reaches-return` | With a ready trace, the fresh cons path runs six instructions to the return address with its exact register and store effects. |
| `collection-forward-installs-header-marker-and-copies-header` | A fresh header installs the forwarding word, copies the original header and advances the destination cursor to its payload. |
| `collection-forward-tests-payload-count`, `collection-forward-enters-header-payload` | A zero count selects return. A positive count enters the loop with its source cursor advanced to the first payload word. |
| `collection-forward-mark-string-effect` | The external string path stores one at the mark and returns the same datum word. |

`collection-copy-payload-checked-segment` in `copy-loop.lisp` covers the
header payload loop. Its ready trace has six instructions per word.
`collection-copy-payload-exhausts-count` and
`collection-copy-payload-advances-pc-on-last-word` give the zero count
and fallthrough address at completion. `copied-words.lisp` connects
store effects to observed memory.
`collection-cons-copy-publishes-marker-and-both-fields` gives both
source forwarding words and both destination fields on disjoint
spans. `collection-external-string-keeps-word-and-acquires-mark` gives
the mark, unchanged word and unchanged destination frontiers.
`collection-payload-copies-every-word` relates every destination
payload word to its original source word for disjoint spans.

| Theorem | Statement |
| --- | --- |
| `collection-checked-fresh-cons-matches-discovery` | A checked fresh call installs the abstract cons assignment, gives both source marker words and both destination fields, and advances the cons frontier. |
| `collection-checked-seen-cons-reuses-discovery`, `collection-checked-seen-header-reuses-discovery` | A checked call on a recorded source returns its assigned datum word and preserves memory and both frontiers. |
| `collection-fresh-header-prepares-copy-and-installs-marker`, `collection-checked-fresh-header-matches-discovery` | A fresh call installs the source marker and the destination header before the payload loop. The checked call returns the assigned datum word and advances the header frontier by the rounded object size. |
| `collection-fresh-header-call-publishes-and-copies-entire-object` | With disjoint spans, the full fresh path leaves the marker at the source and preserves the original header and every payload word at the destination. |
| `collection-checked-fixed-forward-preserves-word-and-marks-external` | The immediate, static cons and static header paths return the original word and preserve memory. Both external string paths return the original word and set the mark. All these paths preserve the frontiers. |
| `collection-placed-cons-forward-is-ready` | Placed cons code and covered source and destination spans give a ready trace for the fresh or reuse path, with the return address outside that trace. |
| `collection-placed-payload-copy-is-ready` | The placed copy-loop instructions and covered payload spans give a ready trace for the entire payload copy. Each iteration preserves placement and advances the spans until the exit. |
| `collection-placed-payload-copy-preserves-placement` | Copying an admitted writable payload preserves the placement of any other decoded trace. |

The full forwarding paths are in `forward-calls.lisp`,
`header-calls.lisp` and `fixed-calls.lisp`. The readiness proofs
are in `forward-placement.lisp`.

## Roots, scan order and value views

`runtime-layout.lisp` assembles and decodes the Linux system code and
the full runtime in their order in `compile-items`. It supplies the
relative branch offsets for the fixed runtime text. The local labels
for the generated entry and static data complete the references from
the entry code. `scanner.lisp` uses the runtime's decodings.

| Theorem | Statement |
| --- | --- |
| `collection-tests-pending-request-size` | The initial request comparison selects the datum-size exit label when the request exceeds four gibibytes. |
| `collection-initializes-destination-cursors` | The destination scan cursors start at the two allocation frontiers given by the other space. |
| `collection-visits-dynamic-root-first`, `collection-rewrites-dynamic-root-before-visiting-stack` | The dynamic symbol table word is forwarded, its result is stored, and the value-stack cursor is initialized. |
| `collection-scan-selects-pending-conses-first`, `collection-scan-tests-pending-headers` | Pending conses have priority. With neither type pending, the scanner selects the finish label. |
| `collection-scan-opens-header-payload`, `collection-scan-skips-raw-payloads` | The header supplies the next cursor and the payload cursor. A string or an integer returns directly to the scan selection. |
| `collection-slot-loop-opens-forwarding-call` | A pending stack slot or header field supplies the forwarder's word and return link. |
| `collection-slot-loop-stores-and-advances`, `collection-slot-loop-ends-at-cursor-limit` | At the return cutpoint, the loop stores the word and advances its cursor. The cursor limit transfers control to the scan selection. |
| `collection-scan-cons-advances-to-first-field`, `collection-scan-cons-stores-first-and-forwards-second`, `collection-scan-cons-stores-second-and-resumes` | The cons cursor descends by one cell. The scanner forwards and rewrites each field in order, then resumes scan selection. |
| `collection-slot-store-commits-returned-word` | The continuation of either slot loop writes the forwarded word and preserves disjoint words. |
| `collection-slot-iteration-forwards-and-commits` | Ready call, forwarding and continuation traces compose to advance either slot cursor and write its returned word. |

`graph.lisp` extracts a graph of the original active objects and
external strings from the shared object map and memory. A graph edge
is a reference through a cons field or a header field. String bytes
and integer limbs supply no edges. The roots are the dynamic table and
initialized stack words. `collection-extracted-graph-record-is-scannable`
gives a valid work record for each lookup in the extracted graph.

`work.lisp` models ordered queues for the two scan cursors.
`collection-discover-again-is-idempotent` says that discovering an
address again leaves its first assignment in place.
`collection-scan-one-decreases-work` bounds progress by the sum of
unseen objects and pending queue entries. Discoveries by either cursor
can add work to either queue. `collection-finish-scan-drains-both-queues`
gives empty queues at completion. In `closure.lisp`,
`collection-scan-one-preserves-accounted-record` keeps a record
unseen, pending, or with all fields discovered.
`collection-traversal-assigns-every-reachable-object` gives a
forwarding association to each original graph address on a path from
a root. `collection-finish-scan-keeps-forwarding-association` preserves
each established association through the remainder of scanning.

| Theorem | Statement |
| --- | --- |
| `collection-traversal-forwards-only-reachable-objects`, `collection-published-forwarding-has-root-witness` | Each forwarding entry has a path witness ending at a root, including for graphs extracted from a published heap. |
| `collection-traversal-assigns-each-source-at-most-once` | Forwarding keys are unique and disjoint from the unseen set. |
| `collection-published-graph-fits-four-gibibytes` | The sum of the published movable spans is at most the capacity of a semispace. |
| `collection-published-traversal-places-disjoint-copies` | For a published heap, every moved copy fits at its assigned end of the destination and distinct moved copies have disjoint spans. External strings keep their addresses. |
| `collection-queue-frontiers-select-pending-scan` | A queue is pending exactly when its scan cursor differs in the scanning direction from its allocation frontier. Its head supplies the copy at the cursor. |
| `collection-published-roots-start-valid-scan-cursors`, `collection-scan-one-preserves-pending-span-layout` | Discovery from the published roots initializes the cursor invariant. Taking a queued object and discovering its fields preserves the invariant at the advanced cursor. |

The path witnesses are in `reachability.lisp` and `exactness.lisp`.
The destination bounds are in `space.lisp` and `published.lisp`.
`queues.lisp` relates queued records to the cursor addresses.

`views.lisp` states a relation on old and new words and their object
records. It requires matching tags, pointer ranks and headers,
corresponding references, and equal bytes, signs and limbs for the raw
payloads.
`collection-transport-preserves-view` then gives equal `proof-view`
results, including for vectors and the internal pair view.
`collection-local-copies-imply-recursive-transport` in
`relocated-views.lisp` derives the recursive relation from local copy
conditions on the objects in a pointer-word table.
`collection-local-copies-preserve-valid-root` applies it to a valid
root and its rewritten word.
`collection-local-copies-establish-stack-and-table-contracts` uses
one copy table and the rewritten slots to preserve the initialized
stack prefix and the dynamic table.
`collection-transported-stack-satisfies-prefix-contract` and
`collection-transported-dynamic-root-preserves-table` in
`root-views.lisp` give the shared stack and dynamic table contracts.

## Capacity, release and sweep

| Theorem | Statement |
| --- | --- |
| `collection-finish-tests-capacity` | The final comparison adds the saved request to the bytes retained at both ends and selects the heap-size exit label when the sum exceeds capacity. |
| `collection-finish-computes-next-budget` | The budget is bounded above by four gibibytes and otherwise is the maximum of 64 kibibytes, twice retained bytes and retained bytes plus the request. The new allocation limit debits the retained bytes from that budget. |
| `collection-limit-admits-pending-span` | The arithmetic limit covers the pending span and stays at or below the new cons frontier. |
| `collection-budget-limit-admits-fast-allocator` | The computed limit satisfies the shared fit test for either aligned request kind. |
| `collection-finish-swaps-space-metadata` | The metadata swaps the two spaces and installs the destination frontiers. The retired frontiers remain in the registers used for the release calls. |
| `collection-finish-passes-retired-header-range`, `collection-finish-passes-retired-cons-range` | Each call to `rt:release-range` receives the appropriate pair of retired endpoints. |
| `collection-release-range-selects-call-or-return` | A positive interval calls `sys:release` with its start and byte count. An empty interval selects return. |
| `collection-retired-release-ranges` | Rounding the header frontier up and the cons frontier down covers the occupied ends, within the retired space's page-aligned endpoints. |
| `collection-runtime-page-multiples-are-kernel-aligned` | Every runtime page multiple is aligned for every kernel page size admitted by the model. |
| `collection-clearing-address-range-keeps-other-memory`, `collection-clearing-address-range-removes-its-memory` | Clearing a range removes its addresses and preserves each association outside it. |
| `collection-sweep-tests-list-end`, `collection-sweep-tests-mark` | The sweep tests the list link and chooses retention or removal by the mark. |
| `collection-sweep-unlinks-before-unmap` | The dead mapping is unlinked before the call to `sys:unmap`, with the mapping's address and size in the argument registers. |
| `collection-sweep-keeps-and-clears-marked-mapping` | The keep path clears the mark, adds the mapping size to the retained total and moves to that mapping's link. |
| `collection-sweep-installs-next-string-budget` | The sweep resets the new-mapping count and sets the budget to the larger of the retained mapping bytes and one mebibyte. |
| `collection-finish-selects-pending-allocator` | After the saved request and the frame are restored, the mode selects the header or cons allocator and the pending byte count and link are carried to it. |

The capacity arithmetic is in `budget.lisp`, retirement arithmetic and
memory clearing are in `pages.lisp`, collection finish cutpoints are in
`finish.lisp`, and string sweep cutpoints are in `sweep.lisp`.
`frame.lisp` covers the save and restore cutpoints.
`collection-saves-request-and-frame` gives the eight saved words in
the 64-byte frame. `collection-restores-request-and-frame` loads the
words in reverse pair order and restores the stack pointer.

| Theorem | Statement |
| --- | --- |
| `collection-checked-linux-relinquish-wrapper` | With the required alignment, writable coverage, zero reply and ready trace, the Linux wrapper clears or unmaps the supplied interval and consumes one reply. |
| `collection-empty-release-returns-without-clearing`, `collection-checked-positive-release-restores-caller` | A checked empty interval leaves bytes and replies unchanged. A checked positive interval calls the Linux release wrapper, restores the saved pair and stack pointer, and returns. |
| `collection-positive-release-clears-range-and-restores-frame` | The positive release's memory effect is the saved pair and clearing of the requested interval. |
| `collection-retired-pages-preserve-word-outside-retired-space` | Clearing both rounded retired intervals preserves every disjoint word outside the retired semispace. |
| `collection-sweep-retains-one-mapping-and-resets-mark`, `collection-sweep-discards-one-mapping-and-relinks` | A retained mapping clears its mark and adds its size. A discarded mapping is unlinked and unmapped, and the cursor stays at the link that now points to the next mapping. |
| `collection-checked-sweep-traversal-reaches-accounting` | An admitted finite sweep trace reaches the accounting label with exactly the retained bytes added and one reply consumed per discarded mapping. |
| `collection-disjoint-store-keeps-saved-frame`, `collection-disjoint-clear-keeps-saved-frame` | Stores and page clears that avoid the saved frame preserve its eight words. |
| `collection-stack-reservation-covers-collector-and-nested-call` | The heap layout and entry stack room give the collector and its nested call 80 writable bytes disjoint from the heap and value stack. |
| `collection-fast-allocation-finishes-collector-contract`, `collection-checked-handoff-and-fast-allocation-return` | The allocator handoff and its fast reservation imply `proof-collector-return-p`. The checked prefixes compose to the caller's cutpoint. |

The wrapper and release proofs are in `retirement.lisp` and
`release-call.lisp`. The sweep proofs are in `sweep-rounds.lisp` and
`sweep-traversal.lisp`. The sweep input states the mark, size and
base at each link. Its retention decisions can be selected from the
forwarding map for the external headers. `frame-protection.lisp`
proves the stack span facts. `agreements.lisp` composes byte-span
agreement on memories whose keys are word-width addresses.
`collection-disjoint-word-store-preserves-span-agreement` and
`collection-disjoint-clear-preserves-span-agreement` establish that
agreement for a store or clear outside the span. Byte stores and range
clears preserve the word-width key condition.
`handoff.lisp` uses the shared fast-allocation return contract after
the body establishes the swapped spaces, restored frame and
preserved heap.

## Collector path composition

`header-placement.lisp`, `header-copy-placement.lisp` and
`source-markers.lisp` give the placement and memory conditions at a
forwarding call. A source observation
records the original words before discovery and the marker for its
assigned destination after discovery.

| Theorem | Statement |
| --- | --- |
| `collection-placed-seen-header-forward-is-ready`, `collection-placed-box-marker-test-is-ready` | Placed instructions and readable words give ready traces for header reuse and for the marker test. |
| `collection-placed-header-forward-prefix-is-ready` | Placement and readable metadata and header words give a ready trace through the address checks and dispatch to the fresh or reuse branch. |
| `collection-placed-fresh-header-forward-is-ready` | After the checked dispatch to the fresh-header branch, placement and writable source and destination spans give readiness for the header stores, payload copy and return. |
| `collection-placed-fixed-forward-is-ready` | Placed code and the required spans give ready traces for immediate and static words and both external-string paths. |
| `collection-published-active-object-is-writable-and-in-forwarding-range`, `collection-published-static-object-is-in-unchanged-forwarding-range` | The published layout places each movable source in the writable portion of the forwarding range and each static object in the unchanged range. |
| `collection-published-external-object-has-writable-mark-and-forwarding-range` | Each published external object reaches one of the two external forwarding branches and has a writable mark. |
| `collection-published-fresh-copy-has-writable-destination` | The destination-space invariant gives the next copy a writable span and a word-width exclusive endpoint. |
| `collection-published-movable-source-is-disjoint-from-inactive-copy` | A published movable source is disjoint from every span within the inactive semispace. |
| `collection-fresh-cons-preserves-disjoint-word`, `collection-fresh-header-preserves-disjoint-word` | A word outside the source marker and destination copy retains its bytes through a fresh forwarding path. |
| `collection-cons-forward-keeps-unclobbered-register`, `collection-fresh-header-keeps-unclobbered-register` | Cons forwarding and fresh header copying preserve the caller's scan cursors and link. |
| `collection-placed-cons-discovery-establishes-source-marker-and-pending-copy`, `collection-fresh-header-discovery-establishes-source-marker-and-pending-copy` | A fresh call establishes the abstract assignment, its source marker and the pending copy. The cons path derives readiness from placement and writable spans. The header path accepts readiness or the placement and access conditions for the fresh copy. |
| `collection-unrelated-discovery-preserves-source-marker-invariant` | A discovery at another address preserves a source observation when the observed words are unchanged. |

The collector entry and scan books connect the frame saves, root
dispatch and abstract queues to the instruction sequence. An object
body in `scan-traversal.lisp` supplies a ready trace back to the scan
label and the cursor and allocation-frontier effects of one scan
step. `rewrite-words.lisp` follows the word assignments in the
abstract traversal.

| Theorem | Statement |
| --- | --- |
| `collection-entry-saves-frame-and-selects-request-path` | The initial saves record the eight frame words and the comparison uses the original byte count. |
| `collection-setup-opens-dynamic-root-call-at-empty-frontiers` | The in-bounds branch installs the destination frontiers and both scan cursors and supplies the dynamic root word to the forwarder. |
| `collection-placed-dynamic-root-continuation-commits-returned-word` | With the instructions placed and the two accessed words covered, the continuation writes the returned dynamic root and loads the stack base before entering the root loop. |
| `collection-slot-rewrites-discover-exactly-the-graph-edges` | Discovering references from slots in address order gives the same work as discovering the extracted graph edges. |
| `collection-slot-rewrites-agree-with-resulting-forwarding-map`, `collection-assigned-datum-stays-at-its-destination-through-scan` | The abstract word written at each slot agrees with the resulting map, and later scanning preserves its assigned destination. |
| `collection-checked-slot-rewrites-install-abstract-relocations` | A checked stack or header-field loop installs the abstract relocated word at each slot when its forwarding calls supply the planned words and preserve the array. |
| `collection-machine-selects-next-queued-copy`, `collection-placed-scan-selection-is-ready` | The next queued object is at the address associated with its cursor. With placed instructions the selector reaches that object, or the finish address when both queues are empty. |
| `collection-placed-raw-header-scan-advances-without-rewriting-memory`, `collection-scan-raw-header-establishes-body-post` | The placed scanner advances past a copied string or integer and changes no memory. A matching raw queue entry with no graph edges satisfies the body obligations for the checked scan loop. |
| `collection-script-length-bounded-by-original-scan-work`, `collection-checked-scan-script-reaches-finish`, `collection-scan-script-finishes-at-abstract-allocation-frontiers` | The number of supplied object bodies is bounded by the initial work. Their composition with the selector reaches `rt:collect-finish` with the abstract final frontiers. |
| `collection-traversal-frontiers-count-exactly-assigned-bytes` | The occupied bytes at the destination ends equal the sum of the assigned movable objects' sizes. External assignments contribute zero bytes. |

`marks.lisp` relates the external mark words to the forwarding map.
`release-pair.lisp`, `sweep-contents.lisp`, `sweep-call.lisp`,
`finish-tail.lisp` and `cleanup.lisp` combine the finish paths under
their kernel and trace premises.

| Theorem | Statement |
| --- | --- |
| `collection-external-list-headers-have-clear-marks` | Each header in a published external list starts with a clear mark. |
| `collection-checked-external-forward-preserves-exact-marks` | A checked external forward marks the assigned header and preserves the agreement with assignments at disjoint marks. |
| `collection-unvisited-external-list-has-exact-mark-table`, `collection-checked-external-forward-maintains-mark-table` | A published list starts with all mark words agreeing with the empty forwarding map. A checked external forward maintains that agreement over the list of separated marks. |
| `collection-marked-external-has-published-root-witness`, `collection-published-reachable-external-is-marked` | When the marks agree with the finished map, marked external headers have root path witnesses and each external header on a root path is marked. |
| `collection-checked-retired-release-pair-returns-to-sweep-call`, `collection-retired-release-pair-preserves-frame-and-counts-replies` | The two admitted release calls reach the sweep call site with the machine stack pointer restored and one reply used per positive interval. |
| `collection-retired-release-pair-protects-word-outside-ranges-and-save` | A word outside both retired ranges and the nested save span survives the two calls. |
| `collection-positive-runtime-page-range-admits-relinquish` | A covered positive interval with runtime-page endpoints and a zero reply satisfies the relinquish predicate for every model kernel page size. |
| `collection-sweep-traversal-links-survivors-and-clears-their-marks`, `collection-sweep-traversal-removes-exactly-discarded-regions` | A sweep of admitted separated mappings links surviving mappings in order, preserves their sizes, clears their marks and removes the discarded intervals. |
| `collection-sweep-call-returns-and-debits-kernel-replies` | The full sweep restores its link and stack pointer, resets the new-mapping count, installs the budget from retained bytes and consumes the discard replies. |
| `collection-sweep-call-preserves-word-outside-its-write-spans` | The sweep leaves a word unchanged outside its save pair, list links, mapping spans and accounting words. |
| `collection-checked-restoration-hands-request-to-allocator` | The restore and dispatch instructions recover the request and mode and reestablish the caller's register frame from the saved words and the unchanged-register premise. |
| `collection-checked-finish-cleanup-restores-frame-and-selects-allocator` | Starting after the metadata swap, the two releases, sweep and restoration compose to the allocator selected by the saved mode. Disjoint write spans protect the collector frame through the calls. |

### Scan memory invariant

`collection-scan-memory-p` relates the original heap to the world at
scan selection. A pending copy has its original payload words. A
processed copy has its relocated field words. A raw string or integer
keeps its payload words throughout. The same work state describes the
source markers, external marks and committed root words.

| Theorem | Statement |
| --- | --- |
| `collection-writing-the-abstract-rewrites-commits-all-fields`, `collection-later-scan-preserves-committed-fields` | Installing the abstract rewrite list commits the slots. Later discoveries preserve their assignments and preserve the slot condition when its words stay unchanged. |
| `collection-graph-domain-supplies-known-slot-sources`, `collection-field-discovery-keeps-graph-domain`, `collection-scanning-keeps-graph-domain` | Every movable reference in a slot belongs to the original graph. Initial knowledge of that graph is sufficient for the slot discovery premise and persists through discovery and scanning. |
| `collection-scan-keeps-unselected-source-pending`, `collection-scan-cannot-requeue-a-committed-source` | A round leaves the other queued sources pending and does not queue a source that has already been processed. |
| `collection-selected-slot-discovery-is-abstract-scan`, `collection-selected-copy-becomes-committed-by-its-field-rewrites` | Rewriting the selected object's slots after removing it from its queue gives the same discoveries as an abstract scan round and commits those slots. |
| `collection-placed-cons-scan-opens-first-forwarding-call`, `collection-placed-cons-scan-opens-second-forwarding-call`, `collection-placed-cons-scan-stores-second-and-closes-round` | Placement and memory coverage check the cons scanner's two call sites and the final continuation. The call sites supply the selected cell's fields in order. |
| `collection-checked-cons-scan-body-stores-both-forwarded-words` | With checked forwarding calls and their stated continuation conditions, the cons scan writes both returned words and returns to scan selection. |
| `collection-admitted-slot-loop-installs-entire-plan`, `collection-checked-slot-loop-establishes-committed-fields` | The checked stack or header-field loop installs the entire planned array and commits its fields when the call results agree with the abstract rewrites. |
| `collection-dynamic-and-stack-rewrites-start-published-traversal` | Discovering the dynamic root and then rewriting the initialized stack in order produces the work state used to start the published-graph scan. |
| `collection-unselected-copy-observation-survives-scan`, `collection-scan-round-preserves-memory-invariant` | An unselected copy with unchanged bytes keeps its observation. The root, source and copy observations hold after a round given its stated writes and preservation conditions. |
| `collection-checked-scan-reaches-finish-with-observed-memory` | Checked object bodies with the required memory effects reach the finish label with the observations for the completed work state. |
| `collection-assigned-word-table-reuses-one-relocation`, `collection-committed-slots-supply-copy-table-edges` | The table constructed from original words gives each assigned word its relocation, and committed slots satisfy the table's field relation. |
| `collection-committed-roots-supply-stack-and-table-contracts` | Committed dynamic and stack roots satisfy the preservation contracts when local copies validate the constructed word table. |
| `collection-completed-cons-observation-validates-local-copy`, `collection-completed-reference-header-observation-validates-local-copy` | A completed cons or reference-bearing header satisfies the local copy condition with the stated destination records, spans and header shape. |

### Sweep list invariant

The sweep snapshot records the links, sizes and marks of the
unvisited mappings. At the loop label, the current link is writable
and separate from the unvisited mappings. The invariant also bounds
the retained bytes and supplies a zero reply for each pending unmap.

| Theorem | Statement |
| --- | --- |
| `collection-unmapping-keeps-regions-well-formed`, `collection-unmap-keeps-instruction-placement` | Removing a writable interval preserves well-formed regions and preserves placed instructions. |
| `collection-placed-sweep-terminator-is-ready`, `collection-placed-sweep-retain-round-is-ready`, `collection-placed-sweep-discard-round-is-ready` | The terminating, retaining and discarding paths are checked from placement, coverage and the applicable unmap conditions. |
| `collection-separated-store-preserves-sweep-snapshot`, `collection-separated-unmap-preserves-sweep-snapshot` | A disjoint store or unmap preserves the links, sizes, marks and coverage of the unvisited mappings. |
| `collection-published-sweep-records-match-links-sizes-and-marks`, `collection-published-sweep-record-uses-forwarding-map` | The published list, preserved metadata and exact external marks give the snapshot with the forwarding map's retention decisions. |
| `collection-published-sweep-records-name-exact-mapping-regions`, `collection-sweep-exact-regions-and-snapshot-give-disjoint-spans` | The published list names its exact writable mapping regions. A finite snapshot of exact regions in the checked region list gives disjoint mapping spans. |
| `collection-published-list-supplies-sweep-loop-invariant` | Preserved published links and sizes, exact marks, alignment and the stated entry and reply conditions establish the loop invariant. |
| `collection-published-sweep-decision-matches-root-reachability` | Each retained header has a path witness from a published root, and a listed header on a graph path from a root is retained. |
| `collection-sweep-round-maintains-unvisited-list-invariant`, `collection-sweep-invariant-supplies-checked-traversal` | A checked round reestablishes the invariant for the remaining unvisited list. The initial invariant supplies the whole loop trace. |
| `collection-sweep-from-snapshot-reaches-accounting-with-exact-effects` | The sweep reaches accounting, clears survivor marks, links survivors in order, removes discarded regions and uses one kernel reply per discarded mapping. |
| `collection-placed-sweep-prologue-is-ready`, `collection-placed-sweep-epilogue-is-ready` | Placed instructions and covered frame and accounting spans check the save and restore paths. |
| `collection-sweep-invariant-protects-caller-link-to-accounting` | The loop reaches accounting with the saved link intact when its writes and unmappings avoid the nested frame. |
| `collection-placed-sweep-call-returns-from-loop-invariant` | The placed sweep returns from the snapshot and boundary conditions with the caller's frame restored, the next string budget installed and the exact kernel reply and region effects. |

## Size diagnostics

`diagnostic-write.lisp` models the Linux write loop on descriptor 2.
A positive short reply advances the buffer and decreases the
remaining count. A zero reply or a Linux error selects the failure
continuation. The diagnostic still attempts the newline and exits
with the saved status. The checked paths require trace readiness and
an admissible reply sequence for both writes.

| Theorem | Statement |
| --- | --- |
| `collection-write-round-consumes-reply`, `collection-write-loop-reaches-restore` | A round consumes its reply and advances the buffer or selects failure. The finite loop reaches restoration with the expected unused replies. |
| `collection-diagnostic-write-all-returns` | The write call restores its stack pointer and saved registers and keeps descriptor 1 output unchanged. |
| `collection-checked-size-diagnostic-exits-with-status-three` | Both admitted size diagnostics reach Linux exit status 3 with descriptor 1 still empty. |
| `collection-oversized-request-path-stops`, `collection-excess-retention-path-stops` | The diagnostics compose with the size comparison at collector entry or the retained-size comparison at `rt:collect-finish`. |
| `collection-collector-diagnostic-stack-covers-both-frames` | With 96 bytes of room below collector entry, the heap layout gives writable spans for the 64-byte collector frame and 32-byte diagnostic write frame. |

## Checked examples and open goals

`examples.lisp` runs the checked Linux model on an assembly fragment
containing the collector, its wrappers and its diagnostic routines.
`collection-example-mixed-return` checks both allocation modes on
conses and headers that discover one another, repeated roots, a live
external string and a dead mapping. Each check applies
`proof-collector-return-p` to its initial and final worlds and checks
sharing, the address of the reserved span, release of the retired ends,
and the survivor's cleared mark. `collection-example-large-request-stops`
checks status 3 both for an oversized request and for a request that
overflows capacity together with the retained bytes.

`collection-sweep-snapshot-example` starts at the sweep loop with
placed runtime code and a snapshot derived from the published
graph. It checks a discard followed by a retain, the cleared
survivor mark, the removal of the discarded mapping and the use
of the supplied kernel reply.

`collection-unaligned-external-example` gives `rt:sweep-strings` one
unmarked external string in a heap accepted by `proof-heap-p`. Its
mapping base is eight bytes past a kernel page boundary. The sweep's
`munmap` reaches `:kernel-contract`. The needed premise is that each
external mapping's base is a multiple of the kernel page size. Adding
`(equal (mod head (proof-world-page-size world)) 0)` for each nonzero
head in `proof-external-objects` would supply it from the shared heap
predicate. The mapping rules already demand page-aligned bases from
successful mapping replies.

`collection-no-frame-space-example` starts an empty valid heap at
`rt:collect` with the machine stack pointer at the bottom of its
mapping. The checked step stops with `:fault` on the first save.
The successful collector entry needs to require
`(<= (+ (- (proof-machine-limit world) *proof-machine-margin*) 80) sp)`,
where `sp` is the entry machine stack pointer. The package gives this
premise in `collection-collector-stack-room-p`.
`collection-diagnostic-needs-more-stack-example` starts a valid heap
with 80 bytes below `sp` and a request above the datum-size bound.
The second save in `rt:write-all` faults before any diagnostic reply
is consumed. For entries that can diagnose a size error, the same
entry bound uses 96 bytes.

`collection-noncanonical-memory-key-example` exhibits a failure of
byte-span agreement to compose for raw model memories. The first
memory contains a rational key whose byte lookup aliases address zero.
Requiring the keys of every memory association to be unsigned 64-bit
integers in the heap interface would supply the
`collection-memory-keys-p` premises used by the handoff proof.

The full published-heap theorem for `rt:collect` remains open.
The root loops must establish the scan memory invariant at the
first selection label. Each actual forwarding call must supply
the invariant's local writes, preservation conditions and access
premises. The finished observations still need to validate a
complete local copy table and the new published object map. At
the sweep call, the caller must preserve the list metadata,
establish exact marks and supply the sweep entry conditions.
The allocator handoff must reestablish the published heap and
preserved spans. The cleanup and diagnostic theorems require
their stated trace premises.
