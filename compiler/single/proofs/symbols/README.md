# Symbols, package operations and interning

The books specify package queries in the ACL2 Core evaluator, interpret the
symbol and table representations in the heap model, and prove instruction
segments in the checked A64 model. An instruction segment begins at one
address and ends at a specified address or machine stop. The instruction
proofs use the compiler's assembled words and the model's decoder. Their
placement and access hypotheses require the instructions to be in executable
memory and their data accesses to be permitted.

## Source semantics and object representation

| Theorem | Conclusion |
| --- | --- |
| `symbols-package-query-implements-core` | The package table gives the result of `PKG-IMPORTS` and `PKG-WITNESS`, covering visible packages, hidden packages, absent names, and the nonstring defaults. |
| `symbols-package-name-implements-core` | A symbol gives its visible home package name or `:no-value` if its home package is hidden. A nonsymbol gives the empty string. |
| `symbols-name-of-nonsymbol-implements-core` | `SYMBOL-NAME` gives the empty string for a nonsymbol. |
| `symbols-intern-default-implements-core` | `INTERN-IN-PACKAGE-OF-SYMBOL` gives NIL if the name is a nonstring or the package designator is a nonsymbol. |
| `symbols-intern-on-static-hit-implements-core` | A binding at the selected static key gives the result of interning, including the symbol's original home package in the import case. |
| `symbols-intern-on-static-miss-is-home` | If the selected static key is absent, the interned symbol belongs to the designated package and has the requested name. |
| `symbols-intern-on-dynamic-hit-implements-core` | After a static miss, a resident symbol with the requested spelling and home package is the result of source interning. |
| `symbols-only-symbols-have-symbol-headers` | A represented value is a symbol exactly when its word is a boxed reference with the symbol header type. |
| `symbols-published-symbol-fields` | A represented symbol's name field represents its source name, and its package field represents the number of its home package. |
| `symbols-represented-string-layout` | A represented string has the string header type and its value is the string loaded from the payload. |
| `symbols-static-package-row-fields`, `symbols-static-package-row-witness-tests-visibility` | The shared static table predicate gives the name, imports, and witness fields at byte offsets 8, 16, and 24 in each package row. The witness word equals the canonical NIL word exactly for a hidden row. |
| `symbols-canonical-symbol-word`, `symbols-canonical-immediate-integer-word` | A valid object map gives each symbol a unique word. The view of an immediate integer determines its tagged word. |
| `symbols-static-view-in-live-objects`, `symbols-static-package-row-fields-in-live-objects` | Values in the static object map retain their views in the full valid object map. In particular, the name, imports, and witness fields still represent the package row's source values. |
| `symbols-package-row-slot-agrees-with-static-vector`, `symbols-static-package-vector-provides-finder-rows` | The numbered row helper addresses the indexed vector slot. The static package vector supplies the addresses, length, and name bytes read by the finder, given the address bound. |
| `symbols-static-addressed-rows-select-source-package`, `symbols-query-data-agreement-from-static-map` | Searching the row bytes selects the same package as the source package list. The static object map supplies the query's field and visibility data in the saved-memory state. |

The source statements use the shared program and package agreement. The
static-hit and static-miss statements use the shared static bucket and import
agreements.

## Lookup, insertion and growth

| Theorem | Conclusion |
| --- | --- |
| `symbols-machine-name-hash-agrees` | The two wrapped 64-bit additions per name byte compute the model's polynomial hash. |
| `symbols-machine-static-hash` | Masking the name and package hash to 12 bits gives the static bucket number. |
| `symbols-machine-tagged-hash` | The tagged result of the machine hash equals the tagged representation of the signed cached hash. |
| `symbols-machine-dynamic-hash` | Shifting the tagged hash and applying a power-of-two bucket mask selects the same bucket as the signed cached hash. |
| `symbols-intern-static-slot-address-agrees-with-vector`, `symbols-dynamic-slot-address-agrees-with-key` | The static address calculation selects the corresponding vector slot. For a power-of-two capacity and a bounded valid span, the dynamic address calculation selects the slot for the decoded name and package key. |
| `symbols-dynamic-chain-terminates` | A valid decoded chain reaches NIL after exactly its number of links. |
| `symbols-physical-static-chain-terminates`, `symbols-physical-dynamic-chain-terminates` | The machine's link fields for a represented bucket reach the canonical NIL word after exactly the number of decoded entries. |
| `symbols-dynamic-entry-fields-agree`, `symbols-dynamic-table-word-encodes-size-and-count` | The physical entry words represent its symbol, cached hash, and next entry. An initialized table's header and tagged count represent its bucket count and number of bindings. |
| `symbols-physical-static-entry-gives-binding-fields`, `symbols-physical-dynamic-entry-gives-binding-fields` | The fields loaded by the two machine scans represent the corresponding binding data in the decoded views. |
| `symbols-lookup-binding-implements-membership` | For a valid table and in-range hash index, scanning the selected bucket finds the given home symbol exactly when it belongs to the table. |
| `symbols-physical-static-chain-finds-source-binding` | With the lookup name and package in the machine inputs, a physical static scan finds a word exactly when the decoded bucket contains the source key. Its returned word represents the binding in that bucket. |
| `symbols-physical-dynamic-entry-represents-home-key`, `symbols-physical-dynamic-chain-finds-decoded-binding` | The entry's fields provide the decoded symbol, cached hash, name, and home number. The physical scan selects a word exactly when the decoded scan finds a binding and returns that binding's representation. |
| `symbols-static-probe-from-static-map`, `symbols-dynamic-probe-from-live-table` | When the probe registers hold the selected head and key, the static and dynamic heap representations provide the chain length and lookup answer. |
| `symbols-fresh-binding-preserves-dynamic-table` | Inserting a previously absent home symbol into the selected decoded bucket adds one binding, preserves the vector's bucket count, and preserves uniqueness. |
| `symbols-doubling-preserves-dynamic-table` | Initializing a NIL table gives 16 buckets. Doubling an initialized table preserves its invariant, uniqueness, entry count, and all its bindings. |
| `symbols-published-root-reaches-dynamic-symbol` | Every dynamic symbol object in a valid heap has a path through a bucket and a finite number of links in the decoded root view. |
| `symbols-published-root-reaches-canonical-word` | Following the physical links along such a path reaches the one word that represents the symbol in the object map. |
| `symbols-collector-return-preserves-bindings` | Under the shared collector return contract, the dynamic table yields the same symbol bindings after collection. |

The insertion and growth operations in `table.lisp` transform decoded heap
views. `proof-dynamic-entries` checks the count against the entries, requires
a power-of-two bucket count, derives the mask from that count, checks the
bucket of each binding, and excludes duplicate symbols.

## A64 execution and source values

| Theorem | Conclusion |
| --- | --- |
| `symbols-replay-is-segment`, `symbols-replay-is-advance` | With the placement, access, and control hypotheses, replaying a decoded path agrees with the checked stepper. |
| `symbols-read-written-bytes`, `symbols-disjoint-read-and-write` | Reading a word after writing it gives its low bits for the specified width. Writing a disjoint span preserves the bytes of the read span. |
| `symbols-machine-stack-writes-preserve-fixed-heap` | Word stores confined to the reserved machine stack preserve the fixed heap spans and external mappings under the heap layout and memory address conditions. |
| `symbols-run-symbol-view`, `symbols-symbol-view-agrees-with-value` | The helper returns the symbol header address in X1 or zero, follows the return link, and preserves memory and registers other than X1 and X2. The result agrees with the represented value's source type. |
| `symbols-run-string-view`, `symbols-string-view-agrees-with-value` | The helper returns the payload address and byte length of a represented string in X1 and X2, or two zero words for the other cases. The byte list at the returned address represents the source string. |
| `symbols-run-package-row`, `symbols-package-row-slot-for-tagged-number` | The helper converts the tagged package number to the slot address in X1, returns the row address in X0, and preserves other registers, flags, and memory. |
| `symbols-run-bucket-address`, `symbols-vector-header-gives-dynamic-mask` | The vector header supplies the dynamic mask, and the tagged hash selects the address of a bucket in X4. X3 holds the mask. |
| `symbols-run-find-setup`, `symbols-run-find-iteration`, `symbols-run-find-result` | The package finder saves its frame, initializes the slot cursor and limit, scans the vector, passes the candidate bytes to `rt:equal-bytes`, and returns a matching row address or zero on exhaustion. These statements specify the individual segments. |
| `symbols-run-find-step`, `symbols-run-find-scan`, `symbols-run-find-package` | Under agreement with the static package vector and the byte-equality contract, the finder returns the first matching row address or zero, restores the saved registers and stack pointer, and leaves memory unchanged outside its saved frame. |
| `symbols-run-query-wrapper`, `symbols-run-query-setup`, `symbols-run-query-dispatch` | The public package-query entries select the field offset, save the query and frame, and route the result of `rt:string-view` to package search or the immediate NIL path. |
| `symbols-run-query-default`, `symbols-run-query-string-continuation` | The default and string paths return a result and restore the frame, or preserve the argument needed by the diagnostic entry. |
| `symbols-run-package-query`, `symbols-run-public-package-query` | The checked package-query body and public entries compute the selected row field or default and restore the caller's frame. A failing name reaches the corresponding diagnostic entry with the original datum. |
| `symbols-package-query-result-implements-core` | Under the static row data agreement, a returned word represents the `core-primitive` result. The hidden and absent names give `:no-value` and route the original datum to the corresponding diagnostic entry. |
| `symbols-public-package-query-contract` | The public package-query entries satisfy the shared return predicate when the package row and saved-memory agreements hold and the stack writes preserve the heap. |
| `symbols-public-package-query-with-static-map` | The public package-query return contract follows using the static object map in the saved state, the argument's runtime type, the finder execution premises, and heap preservation. |
| `symbols-run-name-continuation`, `symbols-run-package-name-continuation` | The name continuation loads the symbol's name or calls the empty-string entry. The package-name continuation loads the visible name or passes the symbol to the hidden-package diagnostic. |
| `symbols-run-symbol-name`, `symbols-run-symbol-package-name` | The checked public routines save and restore the link frame, return the correct field word for a symbol, or transfer to the empty-string or hidden-package entry. |
| `symbols-visible-query-return-implements-core`, `symbols-hidden-or-absent-query-implements-core` | With row agreement, the selected field represents the source result, or the diagnostic target and its argument correspond to a source `:no-value` result. |
| `symbols-symbol-name-return-implements-core` | The name returned by the symbol continuation represents the name in the ACL2 Core evaluator. |
| `symbols-symbol-name-result-implements-core`, `symbols-symbol-package-name-result-implements-core` | For represented symbols, the public routines return the source string, or route a hidden symbol to the diagnostic entry with its original datum. |
| `symbols-package-name-data-from-static-map` | The symbol's represented home number selects the indexed static row. The saved memory provides the name field and the witness test for that row. |
| `symbols-name-of-symbol-runtime-contract`, `symbols-name-of-nonsymbol-runtime-contract` | The name primitives satisfy the shared return predicate for symbols that give a source value and for nonsymbols, given the heap-preservation hypotheses and, on the nonsymbol paths, the empty-string constructor contract. |
| `symbols-run-intern-front`, `symbols-intern-front-selects-argument-path` | The checked prologue saves three register pairs and selects rejection or hashing according to the represented argument types. |
| `symbols-run-intern-reject`, `symbols-run-intern-return`, `symbols-run-intern-default` | The two exits restore the stack pointer and six saved registers. From entry, a nonstring name or nonsymbol designator returns NIL to the caller. |
| `symbols-run-hash-loop-iteration`, `symbols-run-hash-iterations` | The checked name-hash loop consumes the input bytes, computes the model's 64-bit hash, leaves its index at the length, and transfers control to the bucket selection. |
| `symbols-run-intern-select-static-bucket` | The checked hash loop and bucket selection leave the selected static head and the tagged cached hash in registers. |
| `symbols-run-intern-name-check`, `symbols-run-intern-chain` | The name check tests length and bytes using the byte-equality contract. A finite static or dynamic bucket scan selects its first matching word or establishes that the chain has no match. |
| `symbols-run-intern-dynamic-entry`, `symbols-run-intern-probes` | After a static miss, the dynamic root and masked bucket select the next chain, or lead directly to creation for a NIL table. The scans prefer the static binding and enter creation only if neither lookup finds a binding. |
| `symbols-run-intern-lookup`, `symbols-run-intern-existing` | The public entry uses the represented name and package number to select and scan the buckets. A hit returns its binding word, restores the frame, and preserves memory outside the save slots. A miss reaches creation. |
| `symbols-intern-default-runtime-contract`, `symbols-intern-existing-runtime-contract` | The interner returns the `core-primitive` result on rejection and on a static or dynamic hit, given the representation agreement and heap-preservation hypotheses. |
| `symbols-intern-return-word-is-canonical` | Every word that represents the returned symbol in the resulting heap is equal to the word returned in X0. |
| `symbols-run-intern-ensure-stack-call`, `symbols-run-intern-root-name`, `symbols-run-intern-allocate-call` | The interner requests a value-stack slot, saves the name there, checks whether the table has space, and requests the 56-byte symbol and entry block at the allocation entry. |
| `symbols-run-intern-ensure-stack-and-root-name`, `symbols-allocator-preserves-rooted-slot-value` | The shared stack-growth contract preserves the inputs to the name save. The shared allocator contract preserves the decoded value of a live stack slot, even if the word in the slot changes. |
| `symbols-run-intern-allocation-return` | The shared allocator return for the 56-byte request supplies the reserved span and enters the symbol initializer. |
| `symbols-run-intern-miss-with-room-to-reserved-span` | From the public entry on a lookup miss, the interner saves the name and reaches the symbol initializer when the selected table already has room, using the shared stack-growth and allocator returns. |
| `symbols-run-intern-miss-with-growth-to-reserved-span` | From the public entry on a lookup miss, the interner saves the name, takes the growth branch, and reaches the symbol initializer after the new table is published. |
| `symbols-run-intern-initialize`, `symbols-run-intern-publish` | In the reserved block, the checked stores set the symbol header, name and package fields, and the entry header, symbol and hash fields. The publication path links the entry to the previous head, stores it as the new head, and increments the tagged entry count. |
| `symbols-run-intern-initializes-fields`, `symbols-intern-prepared-symbol-represents-core-result` | The reserved block contains the six specified words after initialization. Given the ranked record and the preserved name and package fields, X5 represents the source result of interning a new home symbol. |
| `symbols-run-intern-publication-from-reserved-span` | The initializer, bucket call, and publication path reach the return entry with the new symbol word in X0 and the value stack pointer restored after reloading the name. |
| `symbols-run-intern-fresh-tail`, `symbols-intern-fresh-tail-preserves-initialized-fields` | From the reserved block, the checked insertion and epilogue return to the caller with the boxed new symbol. The caller's save slots and the initialized fields survive under the disjointness conditions. |
| `symbols-run-intern-publication-updates-bucket-and-count` | With disjoint publication slots, the entry's next word is the old bucket head, the new head is the entry reference, and the count increases by one tagged unit. |
| `symbols-ranked-slots-decode-to-expected-views`, `symbols-ranked-vector-fields-give-view` | The views of the fields below a vector record's rank determine the vector's view when its header and span have the specified size. |
| `symbols-intern-fresh-tail-publishes-prepended-bucket` | With ranked entry fields and the old head's view preserved, the published head decodes to the old chain with the new symbol prepended. |
| `symbols-ranked-inserted-root-preserves-dynamic-bindings`, `symbols-ranked-grown-root-preserves-dynamic-bindings` | If the published vector has the ranked fields of the insertion or growth operation, its view satisfies the shared dynamic-table preservation predicate. |
| `symbols-intern-reserved-fresh-runtime-contract` | From the allocation continuation on a static miss, the insertion and return satisfy the shared runtime contract given the ranked heap and preserved field and frame conditions. |
| `symbols-intern-with-room-runtime-contract` | When the table already has room, the checked states from the public entry through reservation and insertion give the shared return contract under the allocation, representation, and heap-preservation hypotheses. |
| `symbols-intern-with-growth-runtime-contract` | When the table needs initialization or doubling, the checked states from the public entry through growth, reservation, and insertion give the shared return contract under the growth, representation, and heap-preservation hypotheses. |
| `symbols-run-rehash-prefix`, `symbols-run-rehash-link`, `symbols-run-rehash-entry` | An iteration reads the old link and cached hash, selects the new bucket, makes the entry its head, and advances to the saved next entry. At NIL it transfers to the next bucket without writing memory. |
| `symbols-run-rehash-bucket-step`, `symbols-run-clear-buckets` | The outer rehash step loads the next old head or reaches the growth exit at the end of the vector. The clearing loop writes NIL to every slot in the new bucket span, advancing by eight bytes per store. |
| `symbols-run-rehash-chain`, `symbols-run-rehash-all-buckets` | For lists of old links that agree with the memory at each read, the checked inner and outer loops perform the specified writes and reach the end of the chain or the growth exit. |
| `symbols-rehash-chain-schedule-follows-from-disjoint-link-slots`, `symbols-rehash-chain-preserves-disjoint-word` | An initial snapshot and disjoint link slots give the link values at every read in a chain. The writes preserve any word disjoint from the link slots and the destination buckets. |
| `symbols-rehash-table-schedule-follows-from-disjoint-link-layout`, `symbols-run-rehash-table-from-disjoint-layout` | An initial snapshot of the old heads and links, with disjoint old heads, link slots, and destination spans, supplies the read schedule and establishes the full checked loop's frame. |
| `symbols-run-intern-grow-call`, `symbols-run-grow-allocation-call` | The interner calls the table-growth routine, which saves the new bucket span and return link and requests space for the header, count, and either 16 buckets or twice the old bucket count. |
| `symbols-run-grow-allocation-return` | Under the shared allocator contract and the machine-stack bounds, the reserved vector is available at the header initializer and the saved size and link are intact. |
| `symbols-run-grow-header`, `symbols-run-grow-after-clear` | After allocation the routine initializes the new header. After clearing it either initializes a zero count or loads the old count and the range of old bucket slots. |
| `symbols-run-publish-grown-root` | The growth exit stores the count and root for the new vector and restores its saved link and stack pointer. |
| `symbols-run-grow-table-tail` | From the allocator's return, the checked routine initializes the header, clears the buckets, rehashes the old chains when a table exists, and publishes the root before returning through the saved link. |
| `symbols-run-grow-table-returns-to-interner-allocation` | When the growth writes preserve the saved link, publication returns control to the interner's symbol allocation entry. |

## Open obligations

The public return theorems assume preservation of the
heap and live value stack. A shared heap frame lemma could discharge
`proof-preserved-heap-p` for writes confined to the machine frame below
the caller's stack pointer, with restored registers and valid memory
addresses. The fixed-span theorem gives part of this result. The finder
uses the accessible byte spans and the byte-equality return specified in
`symbols-find-package-input-p` and `symbols-byte-equality-return-p`.
The static vector theorem uses an explicit nonwrapping bound on the
exclusive end address. A shared consequence of `proof-heap-layout-p`
and `proof-static-p` could make that bound available to callers.

The diagnostic proofs reach the entries that print the failing datum.
A general proof of the observable stop needs the printing and write
contracts, including enough stack space and the system call replies.

The interning contracts take the ranked object map and heap preservation
after publication as hypotheses. A remaining obligation is to construct the
ranked map and establish the heap invariant after the actual stores. The
rehash schedule follows from the initial old heads and links and the
disjointness of their spans. A shared heap layout lemma could derive these
premises from the distinct old entry records and the reserved destination
vector. A shared reachability invariant could require each live
value-stack slot to decode
to a source value and prohibit mutable table and entry vectors from being
reachable from source values. This would allow updates to those vectors
while preserving the live source values. Collection is used through its
shared return contract.

## Certification

From the repository root, run the following commands with ACL2 8.7 on `PATH`.

```sh
SBCL_USER_ARGS='--dynamic-space-size 2500' sh compiler/single/proofs/certify.sh --foundations
sh compiler/single/proofs/symbols/certify.sh
sh compiler/test-symbols.sh build/compiler/single/compiler-2
```

On 2026-11-26 ACL2 8.7 printed `Compiler proof foundations certified.` and
certified the 29 symbol books in logic mode. The two assertions in
`examples.lisp` printed `:PASSED`. They execute the assembled runtime in the
checked A64 model, including the package-query defaults and exact
diagnostic bytes and exit status, resolution through an import, and
interning 17 names across the growth from 16 to 32 buckets. The second
assertion checks that re-interning each of the 17 names returns its
original word.

On 2026-11-26 `compiler/test-symbols.sh` reported agreement between the
compiled and reference programs for re-interning 4,000 names, imports and
witnesses, and the three hidden-package diagnostic cases.
