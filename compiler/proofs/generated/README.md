# Generated terms and calls

These ACL2 books cover the compiler's generated code. An assembler item is a
form such as `(:ldr 0 19 8)`. A decoded instruction is the form that the A64
model executes. A cutpoint is an address where `proof-run` stops before
executing the instruction there. A checked path records the decoded
instructions, verifies their placement and memory access in the executing
states, and excludes premature visits to the cutpoints. The execution
theorems use the context agreement and lower-layer contracts in the
[proof plan](../README.md).

## Certification

Run from the repository root.

```sh
SBCL_USER_ARGS='--dynamic-space-size 2500' sh compiler/proofs/certify.sh --foundations
sh compiler/proofs/generated/certify.sh
```

The proof driver stages every book under `build/compiler/proofs/generated/`
and checks that ACL2 8.7 certifies it in logic mode with skipped proofs, added axioms,
and trust tags disallowed. The ACL2 output for each book is beside its staged
copy. The theorem statements below are checked by these commands.

On 2026-11-26 the first command printed `Compiler proof foundations certified.`
The second command certified 103 books.

## Stack depth and source evaluation

| Book | Theorem | Statement |
|---|---|---|
| `stack` | `generated-term-high`, `generated-args-high`, `generated-lambda-high-and-top` | The generator's reported high-water mark is the maximum of its input bound and the depths after all scheduled pushes. Lambda argument generation also returns the scheduled final depth. The schedule covers both conditional arms and the logical half of an `mbe`. |
| `stack` | `generated-term-high-bounds-pushes`, `generated-args-scheduled-top` | Each scheduled push is within the generated term's high-water mark. Ordinary argument evaluation schedules one push per argument, above the incoming depth. |
| `source` | `generated-source-variable`, `generated-source-quote`, `generated-source-if`, `generated-source-lambda` | The source evaluator looks up a variable, returns the quoted datum, selects an `if` arm from the test result, and evaluates a lambda body in the bindings of its formals to the evaluated arguments. |
| `source` | `generated-source-arguments-first-then-rest` | The source evaluator obtains the first operand's value before it evaluates the remaining operands. |
| `source` | `generated-source-call-follows-chain`, `generated-source-defined-call` | An attachment chain consumes one unit of source fuel per edge and passes the same arguments on each edge. A terminal definition binds its formals and evaluates its body with one less unit of fuel. |
| `source` | `generated-defined-call-info-from-agreeing-indexes`, `generated-runtime-call-info-from-agreeing-index` | Given agreeing indexes, call generation obtains the resolved name and arity and uses the routine label when the terminal name is in the primitive or prelude table. |
| `source`, `emission` | `generated-source-mbe`, `generated-term-emission-of-mbe` | The evaluator and generated instruction sequence use the logical body of a recognized `mbe`. |
| `source` | `generated-variable-actual-uses-existing-slot` | A variable actual in a lambda binds its formal to the existing slot and leaves the occupied depth unchanged. |
| `lambda-alias` | `generated-single-variable-lambda-uses-caller-slot`, `generated-single-variable-lambda-emits-body`, `generated-single-variable-lambda-evaluates-body`, `generated-single-variable-lambda-environment` | A lambda with one variable actual compiles its body with the caller's slot bound to the formal. The source evaluates the same binding, and the caller's slot represents it in the body environment. |
| `emission` | `generated-functions-emission`, `generated-prologue-emission`, `generated-defined-call-emission` | The reverse accumulators yield the forward assembler-item sequences for the generated definitions, prologues, and call sites. |

## Instructions, terms, and frames

| Book | Theorem | Statement |
|---|---|---|
| `steps`, `placement` | `generated-advance-of-placed-path`, `generated-placed-path-to-cut`, `generated-prefix-then-segment`, `generated-cut-compose` | A path with checked placements and accesses executes in its stated number of instructions. The first visit to a final cutpoint gives the shared segment predicate. Segment counts compose across a prefix clear of the final cuts. |
| `arithmetic`, `bits`, `comparisons` | `generated-unsigned-as-mod`, `generated-signed-64-of-word`, `generated-logxor-with-mask`, `generated-condition-of-compare` | Unsigned A64 words are residues modulo their width. Signed 64-bit words have the two's-complement interpretation. The all-ones mask gives the bitwise complement. The compare flags implement equality, inequality, and the unsigned higher-or-same and lower-or-same tests. |
| `registers`, `instructions` | `generated-effect-of-branch`, `generated-effect-of-save-frame`, `generated-effect-of-restore-frame` | The decoded branch, pair store, and pair load have the stated PC, link, register, stack, and memory effects. These books also give rules for moves and immediate and indexed word accesses. |
| `memory`, `copy` | `generated-read-after-writing-same-span`, `generated-read-after-writing-disjoint`, `generated-forward-copy-with-overlap` | The byte model reads back the stored bits and preserves disjoint reads. A forward copy with destination at or below its source yields the original source words even when the ranges overlap. |
| `views`, `heap-views` | `generated-immediate-word-view`, `generated-compiled-entry-ignores-other-registers` | Tagged immediate integers have their source value. Heap, value-stack, and binding observations are preserved by register and PC changes that preserve the heap registers, machine stack pointer, memory, and mapping fields those observations use. |
| `object-views` | `generated-static-booleans-in-published-heap`, `generated-published-symbol-has-unique-word`, `generated-nil-has-canonical-word-in-heap`, `generated-published-cons-field-addresses-fit` | Static Boolean views extend to the full published map. Every represented symbol has a unique word in a valid map. In a heap satisfying the shared contract, word 34 represents `nil`, and represented cons fields have nonwrapping addresses. |
| `published-writes` | `generated-published-view-step-outside-copied-destination`, `generated-published-view-outside-copied-destination` | A bounded word copy whose destination is disjoint from the published objects preserves the views of existing words. The recursive statement also covers a disjoint array of slots. |
| `terms` | `generated-variable-immediate-slot-execution`, `generated-small-quote-execution` | A linked non-tail variable load with a slot below 4096, or a quoted raw word below `2^16`, reaches its continuation with the source value in X0 and the input value-stack prefix preserved. The corresponding emission theorems identify these assembler items. |
| `compound-terms` | `generated-if-nontail-emission`, `generated-if-dispatch-in-published-heap`, `generated-if-dispatch-and-selected-arm-return` | A linked conditional dispatch reaches the source-selected arm after its test result is available. A checked returning segment for that arm composes with the dispatch and yields the source result and preserved input prefix. |
| `wide-words`, `addresses` | `generated-wide-word-emission`, `generated-wide-word-load-continuation`, `generated-address-reaches-continuation` | The move-wide instructions emitted for a 64-bit word load it into the stated register. The address sequence then adds or subtracts the byte offset in the requested register, including offsets that require a scratch register. |
| `wide-terms`, `tagged-constants` | `generated-variable-indexed-slot-execution`, `generated-quoted-raw-word-execution`, `generated-tagged-quote-execution` | An indexed variable load and either form of constant-map entry return the source value in X0 and preserve the value-stack prefix. Tagged integer constants cover the full signed immediate range. |
| `operand-stack` | `generated-argument-emission-in-evaluation-order`, `generated-push-appends-operand-word`, `generated-immediate-drop-restores-top` | The emitted argument code evaluates the first operand, pushes it, then generates the remaining operands. A checked push appends the operand word to the stack, and an immediate drop restores the requested top. |
| `stack-pop` | `generated-stack-views-have-valid-prefix`, `generated-drop-emission`, `generated-drop-keeps-valid-stack-prefix` | A prefix of a represented stack has the same prefix of views. The emitted drop sequence preserves the heap contract, the retained views, and X0, for immediate and wide adjustments. |
| `operand-registers` | `generated-argument-register-emission`, `generated-argument-registers-load-views` | The generator loads consecutive frame slots into consecutive registers. The checked preparation establishes the argument views for a runtime call, including when the source slots use wide offsets. |
| `frames`, `prologue` | `generated-prologue-machine-stack-check`, `generated-prologue-save-slot-words`, `generated-prologue-deep-call` | The stack check selects the frame save or the depth-stop call. A permitted save stores X19 and X30 in the new 16-byte frame. The depth-stop call reaches `rt:deep` with the failed machine-stack bound. |
| `prologue` | `generated-prologue-value-stack-check`, `generated-prologue-grow-link`, `generated-prologue-sets-immediate-frame-base` | With an immediate address adjustment, the value-stack check computes the required top and chooses the growth edge when it exceeds X24. The linked growth call supplies that demand and a return link. The immediate frame-base calculation sets X19 to X25 less the argument bytes. |
| `growth` | `generated-grow-return-preserves-prologue-frame` | Under the growth return contract, a successful growth covers the demand, preserves the saved machine frame and value-stack top, and returns to the supplied link. |
| `wide-prologue` | `generated-prologue-checks-full-width-demand`, `generated-full-prologue-when-frame-fits` | The value-stack check handles a full-width demand and selects the growth edge or the continuation. When both stacks have room, the checked prologue saves the machine frame and sets the value-stack frame base, including with wide offsets. |
| `prologue-paths`, `prologue-flow` | `generated-prologue-reaches-growth-entry`, `generated-growing-prologue-enters-body`, `generated-depth-stop-composes-with-runtime` | The checked entry code computes the exact growth demand and installs the runtime link. Given the growth segment and return contract, the prologue reaches the body with the saved frame intact. A failed machine-stack check composes with the depth-stop runtime segment. |
| `calls`, `frames` | `generated-defined-call-establishes-entry`, `generated-defined-call-returns-to-continuation`, `generated-return-restores-frame` | Ordinary `BL` preserves the incoming arguments and establishes the compiled-entry contract at the callee. A callee that meets the compiled-return contract returns to the instruction after the call, pops the arguments, and preserves the lower prefix by value. The generated return sequence observes the saved machine frame and preserves the result in X0. |
| `copy-path`, `calls` | `generated-copy-immediate-path-words`, `generated-tail-epilogue-installs-callee-frame` | The immediate-offset load and store sequence copies the original arguments. The tail epilogue sets the new value-stack top, restores the saved frame, and jumps without changing the restored link. |
| `tail` | `generated-tail-immediate-emission`, `generated-tail-immediate-call-transfer` | For arities below 512 the generated sequence reaches the target with the original argument words compacted at the current frame base and the saved return link installed. The proof allows an overlap of the source and destination slots and a callee with more arguments than the caller. |
| `indexed-copy`, `indexed-tail` | `generated-indexed-copy-transfers-words`, `generated-indexed-tail-emission`, `generated-indexed-tail-call-transfer` | The same transfer holds for a 64-bit argument byte count under the placement and nonwrapping span premises. The execution uses the register-offset loads and stores when the offsets are too wide for the immediate instruction. |
| `root-transfer` | `generated-stack-views-are-word-views`, `generated-indexed-tail-enters-with-argument-views` | The stack views are the views of its words in order. The tail transfer establishes the compiled-entry contract when the resulting heap is valid and the published views of the argument words are preserved. |
| `tail-roots` | `generated-indexed-tail-observes-copied-memory`, `generated-indexed-tail-preserves-published-word-views`, `generated-indexed-tail-establishes-entry-with-disjoint-objects` | The executed tail sequence has the memory of the abstract word copy and preserves the heap base. Disjointness of the destination and the published objects suffices for preservation of existing word views. With a valid resulting heap the moved arguments satisfy the compiled-entry contract. |
| `tail` | `generated-tail-callee-return-observations` | A tail callee satisfying the compiled-return contract returns its value through the original saved link and restores the value-stack top to the original frame base. |
| `inlines` | `generated-consp-emission`, `generated-consp-checked-path`, `generated-routine-noninline-emission` | The inline `CONSP` tests the cons tag and places the corresponding Boolean word in X0. Names outside the inline cases emit a `BL` to the supplied routine label. |
| `list-views`, `pair-access`, `compound-terms` | `generated-cons-word-points-to-two-datums`, `generated-pair-access-in-published-heap`, `generated-identical-word-equality-fast-path` | A represented cons points to two represented datums. In a valid heap, checked `CAR` and `CDR` paths select the corresponding field or return `nil` for an atom. The equal-word path of `EQUAL` returns the true word and its two source values are equal. |
| `arithmetic-paths` | `generated-integer-routine-emission`, `generated-integer-tag-guard-selects-edge` | The compiler emits one-bit tag tests, fast instruction sequences, and a slow call for addition, negation, and signed comparison. The tag tests select the slow edge for an operand without the immediate integer tag, preserving both argument words. |
| `fast-arithmetic`, `arithmetic-paths` | `generated-fast-addition-word-and-overflow`, `generated-fast-negation-word-and-overflow`, `generated-fast-immediate-less-than`, `generated-inline-arithmetic-result-or-slow-edge`, `generated-inline-immediate-less-than-path` | Prepared immediate operands give the encoded arithmetic result or the overflow branch with their original argument words. Signed comparison flags give the source order, and the checked comparison path returns the corresponding Boolean word. |
| `routines` | `generated-routine-bl-establishes-entry`, `generated-routine-returns-to-continuation` | A linked routine call establishes the runtime-entry contract from the prepared register arguments. The runtime-return contract supplies a result in X0, returns to the saved continuation, and preserves the input prefix by value. |

## Heap preservation and generated boundaries

| Book | Theorem | Statement |
|---|---|---|
| `stack-prefix`, `prefix-suffix` | `generated-prefix-preserves-aligned-environment`, `generated-compiled-arguments-survive-prefix-preservation` | Preserving the views of an aligned prefix preserves the source bindings and argument suffix it represents, including when allocation changes the addresses of represented objects. |
| `memory-frame`, `object-frame`, `static-frame`, `external-frame` | `generated-byte-outside-written-span`, `generated-object-map-outside-written-span`, `generated-static-data-outside-written-span`, `generated-external-mappings-outside-written-span` | Memory outside the write span agrees. Object views, the static data, and external mappings have the same observations under the stack framing premises. |
| `heap-layout-frame`, `heap-update`, `heap-disjoint` | `generated-stack-update-preserves-heap-layout`, `generated-stack-update-preserves-heap-with-valid-roots` | A write confined to either runtime stack preserves the heap layout and existing objects. Valid views for the resulting occupied slots suffice to establish the resulting heap contract. |
| `stack-write`, `capacity` | `generated-push-preserves-heap-and-appends-value`, `generated-scheduled-push-preserves-heap-and-appends-source-value` | The checked push adds the operand's source value and preserves the heap and older slots. A reservation at the generated high-water depth gives space for each scheduled push at its incoming depth. |
| `tail-frame`, `tail-return`, `tail-call-flow` | `generated-indexed-tail-establishes-entry-and-preserves-heap`, `generated-tail-callee-return-is-outer-return`, `generated-tail-call-composes-argument-collection-and-callee-return` | The tail sequence establishes a valid heap and the target's argument views. It preserves the lower prefix and restores SP, X19, and the saved link before jumping. Argument collection and this transfer compose with the callee's return through that link. |
| `prologue-heap`, `prologue-state`, `entry-bindings`, `function-body-entry` | `generated-prologue-frame-save-keeps-valid-heap`, `generated-full-fitting-prologue-establishes-body-entry`, `generated-growing-prologue-establishes-body-entry`, `generated-function-entry-provides-body-environment`, `generated-fitting-definition-prologue-establishes-body-bindings-and-reservation` | The frame save preserves the heap. At body entry the prologue has installed the frame base and preserved the stack arguments. Distinct formals have their source values in consecutive slots. A fitting prologue establishes the reservation for the generated high-water depth. A growing prologue uses the runtime growth return contract. |
| `growth-edge`, `capacity` | `generated-over-reservation-demand-reaches-value-stack-resource-stop`, `generated-successful-growth-limit-covers-its-prior-limit` | A demand above the incoming value-stack reservation reaches the runtime with that bound still violated and composes with its resource exit. Within the reservation, the specified growth limit covers the demand and the previous limit. |
| `return-heap`, `compiled-return` | `generated-return-preserves-heap-and-retained-prefix`, `generated-finish-emits-frame-restore-and-ret`, `generated-finish-establishes-compiled-return-contract` | The generated finish restores the saved frame and link without writing memory. It keeps the retained prefix and X0's value in a valid heap. If the body preserves the protected frame and heap observations, the finish establishes the shared compiled-return contract. |
| `saved-frame` | `generated-operand-push-preserves-saved-machine-frame`, `generated-runtime-and-compiled-returns-preserve-saved-machine-frame`, `generated-saved-machine-frame-preservation-composes` | The value-stack push leaves the saved machine frame intact. Returning runtime and compiled boundaries preserve both saved words in the caller's mapped frame. This preservation composes across successive segments. |
| `protected-frame`, `prologue-heap` | `generated-memory-outside-positive-write-agrees-on-protected-span`, `generated-stack-update-preserves-protected-heap-frame`, `generated-value-stack-update-preserves-protected-heap-frame`, `generated-frame-save-preserves-caller-heap-frame` | A write starting above address zero leaves bytes in disjoint bounded spans intact. A confined stack update disjoint from the saved machine stack, with unchanged streams, preserves the heap-frame contract, including its static byte ranges and caller stack. Value-stack updates are disjoint by the heap layout. The prologue saves its two words below the caller's protected span. |

## Terms, argument lists, and routine results

| Book | Theorem | Statement |
|---|---|---|
| `segments`, `argument-flow` | `generated-segment-composes-with-final-segment`, `generated-evaluated-operand-and-push-compose`, `generated-argument-stages-compose` | Checked segments compose using their step budgets. A returning operand and its push extend the occupied stack with its value. These extensions concatenate in evaluation order. |
| `argument-evaluation` | `generated-argument-trace-evaluates-in-source-order` | A returning trace for the computed operands yields the source list of pushed values in order. In lambda mode, a variable actual uses its existing binding and consumes no push. |
| `simple-registers` | `generated-simple-register-emission`, `generated-simple-registers-load-source-arguments`, `generated-simple-runtime-call-emission` | Direct argument preparation loads variable slots and represented quoted values into successive registers, matching successful source argument evaluation. The emission theorem identifies the routine and finish code that follow the loads. |
| `scope-order`, `scope-tree`, `lambda-slots`, `lambda-environment` | `generated-lambda-arguments-install-aliased-and-pushed-slots`, `generated-lambda-scope-looks-up-formal-slots`, `generated-lambda-body-environment-from-evaluated-actuals`, `generated-function-scope-looks-up-entry-slots` | AVL tree insertion and rotations preserve lookup. A lambda can mix caller-slot aliases and newly pushed actuals. The resulting scope and stack views give the source body environment. Function formals use consecutive slots. |
| `term-flow`, `conditional-flow`, `noncall-terms` | `generated-simple-term-provides-nontail-result`, `generated-if-test-and-dispatch-compose`, `generated-if-true-arm-jump-composes`, `generated-noncall-trace-returns-source-value` | Variables and quotes return their source values. With checked paths for a nested conditional or recognized `mbe`, induction composes the test, selected arm and any required jump. It establishes the continuation, X0 result, valid heap, and preserved prefix. |
| `linked-loads`, `linked-push` | `generated-linked-move-wide-prefix-is-checked`, `generated-simple-operand-has-checked-path-from-linked-bytes`, `generated-push-has-checked-path-from-linked-bytes` | Consecutive linked move-wide instructions form a checked path. The heap supplies read access for bound variables and write access for a push within the current value-stack limit. Executable and writable mappings are disjoint, so the push preserves the next instruction's bytes. |
| `linked-control` | `generated-conditional-dispatch-has-checked-path-from-linked-code`, `generated-linked-if-dispatch-items-have-checked-path` | The laid-out compare, conditional branch, and alternate jump give the checked dispatch path when instruction addresses are clear of prior cutpoints. Only the false arm executes the alternate jump. |
| `lambda-flow`, `lambda-result`, `evaluation-tree` | `generated-lambda-drop-matches-number-of-pushed-actuals`, `generated-lambda-argument-and-body-traces-return-source-value`, `generated-term-and-argument-evaluation-tree-sound` | The drop removes exactly the slots occupied by computed actuals. The body uses the evaluated bindings and returns to the incoming top. Joint induction on source fuel covers terms, ordinary argument lists, and lambda argument lists. Terms include nested lambdas, conditionals, recognized `mbe` forms, calls of routines with a checked routine result, and ordinary named calls with the callee return contract. |
| `conditional-result` | `generated-conditional-evaluation-selects-and-returns-source-value` | Returning test and selected arm segments may change the published object map. Checked dispatch and the optional true-arm jump compose with them and preserve the original stack views. |
| `defined-flow`, `resolved-calls` | `generated-ordinary-call-composes-arguments-link-and-return`, `generated-resolved-defined-term-emits-arguments-and-call`, `generated-resolved-source-call-evaluates-defined-body-at-smaller-fuel`, `generated-resolved-source-call-evaluates-runtime-value` | The checked ordinary call transfers the collected suffix, then consumes it on return. An agreeing resolution index gives the same terminal name. Source evaluation of a resolved definition uses the stored body and strictly less fuel. A terminal routine evaluates to the runtime source value. |
| `named-calls` | `generated-resolved-ordinary-call-returns-source-value` | With checked operand and call placement and the callee's compiled-return contract for the smaller-fuel body result, the enclosing call returns the source term's result. |
| `runtime-flow` | `generated-linked-runtime-call-and-return-compose` | A linked `BL` establishes the routine entry, and a segment meeting the runtime return contract supplies the source value and leaves the caller's stack prefix in place. |
| `prepared-calls` | `generated-collected-arguments-load-runtime-registers`, `generated-simple-evaluated-arguments-and-routine-compose`, `generated-computed-runtime-term-emits-arguments-registers-and-drop`, `generated-computed-arguments-routine-and-drop-compose` | Simple operands load directly before a returning routine. For computed operands, the emitted code loads the evaluated stack suffix into the routine registers, executes the routine, and drops the argument slots while retaining the result and the caller's prefix. |
| `runtime-term` | `generated-resolved-runtime-application-evaluates-source-result`, `generated-simple-runtime-application-returns-source-result`, `generated-computed-runtime-application-returns-source-result` | The terminal primitive or prelude routine gives the source application's value. With a segment returning that routine value, both operand preparation paths reach their source continuation, retain the incoming stack prefix, and represent the source value in X0. |
| `immediate-views`, `equal-paths`, `inline-flow` | `generated-fast-atomic-values-have-canonical-words`, `generated-inline-consp-returns-source-value`, `generated-inline-pair-access-returns-source-value`, `generated-equal-identical-words-return-source-value`, `generated-equal-distinct-words-select-result-or-slow-call`, `generated-equal-slow-path-returns-source-value` | Immediate integers and characters have canonical words. The list operations return their source values. `EQUAL` selects true for identical words, false for a distinct word with an immediate integer or character operand, and the runtime edge for the remaining distinct words. The slow path includes the branch after the runtime return. |
| `number-flow` | `generated-immediate-tag-matches-represented-integer`, `generated-inline-number-selects-source-value-or-linked-call-site`, `generated-inline-number-slow-path-returns-source-value` | The immediate tag agrees with the source representation. Addition, negation, and signed comparison either return the inline source result or reach the slow call with the original argument views. Under the runtime return contract, the slow execution returns the source result to the same continuation. |

## Recursive returns

A recursive ordinary call can visit the same return address in several
different machine frames. `generated-frame-run` stops on a pair containing a
PC and an SP. It uses `proof-step` for each machine transition.
`generated-frame-prefix-and-segment-compose` composes an exact clear prefix
with a frame-aware segment. `generated-frame-segments-compose-under-step-budgets`
also composes segments specified by step bounds.
`generated-address-segment-gives-correct-frame-cut`
converts an address segment when its endpoint has the required SP.
`generated-frame-cut-call-restores-the-original-caller` composes a linked
ordinary call with a return to the original PC and SP under the callee
contract. `generated-resolved-call-with-frame-cut-returns-source-value`
composes argument collection, the linked call, and the smaller-fuel body
result using that return criterion.
`generated-tail-transfer-reaches-original-return-frame` also uses that
criterion for a tail call. It starts with the collected argument suffix,
establishes the callee's entry, and restores the original saved PC, SP,
and lower value-stack prefix under the callee return contract.
`generated-compiled-return-observes-inherited-frame` extracts the restored
registers, stack pointer, and stack prefix from the compiled-return contract.
`generated-body-value-and-finish-establish-frame-aware-return` uses the
body's value and protected frame to prove that the epilogue meets that
contract at the caller's return frame. `generated-fitting-function-path-returns-to-caller-frame`
composes a checked fitting prologue, a returning body segment, and the
epilogue. `generated-fitting-definition-returns-checked-source-body` relates
the composition to the generated definition's arity and high-water depth.
It establishes the body bindings and reservation and returns the source
body's value when the body segment and its preservation conditions hold.

`generated-recursive-cutpoint-needs-restored-stack-pointer` checks an assembled
recursive call with two visits to the return address. The certification
command above checks the following results on 2026-11-26.

| Cut test | PC | SP | X0 |
|---|---:|---:|---:|
| Address alone | `0x1020` | `0x2fe0` | 0 |
| Address and restored SP | `0x1020` | `0x2ff0` | 1 |

## Attachments to `IF`

ACL2 refuses to attach a function to `COMMON-LISP::IF`, and `spec/formats.md`
excludes such an `attach` line. `generated-attachment-to-if-is-refused`, in
`refusals.lisp`, proves that `index-lines` refuses every `attach` line whose
target is `IF`: it gives no definitions, names, attachments, sources,
packages, entry or target, and the compiler writes no executable. The
generator therefore never meets a call whose resolved target is `IF`.

The session below shows ACL2 8.7 refusing the attachment, with an error
finding `STOBJS-OUT` for `IF` (2026-11-26).

```sh
SBCL_USER_ARGS='--dynamic-space-size 2500' acl2 <<'EOF'
(defstub select (x y z) t)
(defattach select if)
(good-bye)
EOF
```

## Open obligations

The term and argument induction consumes checked paths and context agreement.
The full compiler theorem needs a construction of those paths from the linked
output for every accepted term. It also needs a recursive induction that
establishes the compiled-return contract for each named callee at the smaller
source fuel. The fitting-definition composition takes the body's execution
and preservation conditions as premises. The named-call and tail-transfer
theorems take the callee's return contract as a premise. The joint tree still
uses address-only cuts. A recursive body proof must compose with the
frame-aware ordinary and tail return boundaries. The runtime stops and
returns use the imported contracts in the proof plan.

The prologue uses `X23 ≤ SP` at compiled entry. Under the heap layout,
`generated-incoming-machine-bound-prevents-subtraction-wrap` then supplies the
lower bound of 16 needed by the subtraction. Adding `X23 ≤ SP` to
`proof-compiled-entry-p` and establishing it at every generated entry would
discharge the explicit machine-depth premise at those entries.

The push theorem takes the frame reservation at the current value-stack
limit. `generated-equal-return-contract-allows-limit-at-current-top` shows
that `proof-runtime-return-p` for `EQUAL` still holds after setting X24 to the
occupied top of an admissible returned state. Extending the shared returning
heap contract with `proof-stack-limit before ≤ proof-stack-limit after`
would carry the reserved frame bound through routine calls. The compiled
return contract also needs that inequality for callers that use it as an
imported boundary. A shared frame-aware return segment using the restored SP
would express the recursive continuation illustrated above.

The shared byte-span test iterates over map keys. A64 normalizes a
noninteger address to zero when it reads a byte. Testing only unsigned
64-bit address keys in `proof-byte-entries-agree-p` would remove the
positive write-start premise from the protected-span theorem. The prologue
frame save obtains that premise from its machine-stack bound.

The compiler and source model must agree on calls through an attachment to
the conditional primitive before the result theorem can cover that text.
