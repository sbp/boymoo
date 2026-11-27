# Tests, projections and equality

The statements use the checked AArch64 machine and the value, heap and
runtime interfaces in [the foundations](../foundations/). A word is an
unsigned 64-bit register value. A value view relates a word and a heap
to the ACL2 datum it represents. A runtime contract supplies a finite
checked execution segment ending at the incoming return address in X30,
and a result related to the ACL2 Core primitive. Its frame identifies
the registers and flags that may change.

The code placement premises refer to decoded instructions at offsets
from the start of the runtime. `p6-sites` obtains the offsets and words
from the runtime assembler items. Placement includes executable access,
and the selected instruction addresses must differ from the return
address until the return step.

## Main theorems

| Book | Theorem | Statement |
| --- | --- | --- |
| `words` | `p6-odd-word-decodes-to-immediate` | An odd word decodes to an immediate integer, and encoding that integer recovers the word. |
| `byte-views` | `p6-load-equality-is-byte-list-equality` | Two little-endian loads of the same width agree exactly when their byte lists agree. |
| `byte-views` | `p6-loaded-header-fields` | The low byte of a loaded header is its type, and the other seven bytes determine its size. |
| `data-views` | `p6-word-class-of-value` | Each represented datum has the tag and, for a header object, the type required by its ACL2 class. |
| `data-views` | `p6-cons-field-views`, `p6-rational-field-views`, `p6-complex-field-views` | Loading the indicated fields yields the views of the corresponding cons, fraction or complex-rational components. |
| `heap-views` | `p6-heap-has-boolean-views` | The static NIL and T views also hold in the full published object map of a valid heap. |
| `paths` | `p6-read-only-path-runs` | With the decoded instructions placed in executable memory, an accessible path gives exactly the corresponding checked execution. |
| `leaf-routines` | `p6-literal-entry-returns`, `p6-boolean-entry-returns` | The private literal-return entries give their specified constants. `rt:boolean-eq` selects T or NIL from the Z flag. |
| `leaf-routines` | `p6-tag-test-returns`, `p6-header-test-returns`, `p6-number-test-returns` | The tag tests and the private `rt:header-p` and `rt:number-p` entries return the specified booleans, with the declared frames. |
| `state-invariants` | `p6-read-only-datum-return` | A read-only machine return with the represented result satisfies the datum-return interface, including the heap, incoming roots and absence of allocation. |
| `contracts`, `mapped-data` | `p6-leaf-primitive-runtime-contract`, `p6-mapped-leaf-primitive-runtime-contract` | The checked runtime entries agree with `BAD-ATOM<=`, `CAR`, `CDR`, `CONSP`, `CHARACTERP`, `STRINGP`, `SYMBOLP`, `INTEGERP`, `RATIONALP`, `COMPLEX-RATIONALP` and `ACL2-NUMBERP`. The mapped contract obtains load permissions and boolean views from the heap invariant. |
| `mapped-data` | `p6-published-object-contents-are-readable` | The contents of each published static, active or external object are in a readable span. |
| `characters` | `p6-character-primitives-runtime-contract` | `CHAR-CODE` and `CODE-CHAR` satisfy the runtime contract on every represented argument, including the completions at byte code zero. |
| `numeric-projections` | `p6-numeric-type-entry-returns` | The checked `rt:num-type` entry returns X3 equal to 3, 4, 5 or 0 for the specified numeric classes and other data. For a header word, X4 is the header address. |
| `numeric-projections` | `p6-numeric-projection-word-agrees-with-core` | The projection word represents the ACL2 Core result of `NUMERATOR`, `DENOMINATOR`, `REALPART` or `IMAGPART` on every represented datum. |
| `numeric-projections` | `p6-immediate-numeric-projections-runtime-contract`, `p6-numeric-projection-continuations-return` | The projections of immediate integer inputs satisfy the runtime contract. The continuations after the saved link is restored return the result word selected by the type and the requested projection. |
| `machine-stack` | `p6-load-stored-register-pair`, `p6-load-outside-stored-register-pair` | A pair store writes the saved words in order and preserves loads from disjoint spans. |
| `scratch-frame` | `p6-machine-save-room-is-mapped`, `p6-machine-save-pair-leaves-heap-fixed`, `p6-machine-save-keeps-value-stack-storage` | A 16-byte save span starting above address zero within the machine-stack reservation has write access under the heap layout. The save leaves heap and value-stack storage fixed. |
| `numeric-stack-paths` | `p6-numeric-prologue-checked-call`, `p6-numeric-save-and-restore-agree` | The prologue for even words saves X29 and X30 and calls `rt:num-type`. The restore recovers X29, X30 and SP when the saved words are intact. |
| `boxed-numeric` | `p6-boxed-numeric-projection-runs`, `p6-boxed-numeric-projections-with-machine-save-room` | The projections of header, cons and character inputs return to the incoming link with only X0, X3 through X5 and NZCV allowed to change. The only memory writes are the two saves below the incoming SP. With room in the machine reservation, the runtime contract derives the fixed-heap condition and assumes the saves preserve the heap invariant, root views and argument view. |
| `equality-entry` | `p6-equal-same-word-runtime-contract` | Equal input words return T through checked execution, with a frame allowing changes to X0 and NZCV. |
| `equality-entry` | `p6-equal-early-rejection-runtime-contract` | Different tags and distinct immediate words take the checked NIL return paths, which allow changes to X0, X2 and NZCV. |
| `equality-views` | `p6-published-symbols-equal-exactly-by-word` | Within the published object map, two represented symbols agree exactly when their words agree. |
| `equality-views` | `p6-deferred-conjunction-pop`, `p6-defer-cons-second-field`, `p6-defer-numeric-second-field` | Popping a pair exposes one conjunct. Comparing the first fields and deferring the second fields preserves the equality conjunction for the two original values. |
| `equality-views` | `p6-string-equality-by-payload-bytes` | Two string views agree exactly when their declared payload byte lists agree. |
| `equality-work` | `p6-decomposing-datum-pair-reduces-work`, `p6-comparison-work-computes-conjunction` | Replacing a cons, fraction or complex comparison by its field comparisons reduces the natural number of remaining comparison nodes. Processing a list of datum pairs yields their equality conjunction. |
| `bignum-equality` | `p6-boxed-integer-equality-by-header-and-payload` | Two normalized integer views agree exactly when their headers and declared payload bytes agree. The proof accounts for the sign and the unique normalized limb count. |
| `equality-dispatch` | `p6-equal-dispatch-runs`, `p6-equal-symbol-dispatch-uses-published-identity` | The distinct-word classifier runs to the specified comparison block. Its symbol rejection relies on uniqueness of symbol identity in the published map. |
| `equality-header-views` | `p6-equal-header-rejection-agrees-with-core`, `p6-equal-byte-case-agrees-with-core` | A header mismatch implies unequal ACL2 datums. In the string and integer byte cases with matching headers, comparing the declared payload bytes decides ACL2 equality. |
| `equality-fields` | `p6-equal-fields-dispatch-runs` | The field block loads both pairs, selects an unresolved pair, and calls `rt:ensure-stack` when it must defer the second comparison. |
| `equality-stack` | `p6-equal-deferred-push-runs`, `p6-equal-pop-exposes-next-conjunct`, `p6-deferred-pair-store-extends-conjunction` | The checked push and pop write and read the next pair at the stack top. A pair store adds the new conjunct while preserving earlier conjuncts in a fixed reference heap. |
| `equality-stack` | `p6-equal-empty-stack-branches-to-yes`, `p6-equal-epilogue-returns` | Exhausting the deferred stack selects success. The exit blocks restore the saved top and link and return the corresponding boolean. |
| `compare-bytes` | `p6-byte-comparison-block-runs` | Each of the byte comparison loop's six checked paths takes the specified branch or returns. |
| `byte-ranges` | `p6-byte-comparison-runtime-contract` | From two readable spans of the common length in X2 and endpoints below `2^64`, `rt:equal-bytes` returns 1 for identical bytes and 0 otherwise. It preserves memory, mappings, SP and all registers outside X0 through X4. The proof covers partial tails and empty spans. |
| `equality-byte-call` | `p6-equal-byte-call-passes-declared-length`, `p6-equal-byte-result-branches`, `p6-string-equality-by-header-and-payload` | `rt:equal-byte-span` passes the header's length to the byte comparator. Zero selects failure and one resumes the pending comparisons. String equality agrees with comparison of the header and declared payload. |
| `equality-control` | `p6-equal-pair-compares-words`, `p6-equal-second-installs-pair`, `p6-equal-cons-installs-field-addresses` | `rt:equal-pair` branches to `rt:equal-next` when X0 and X1 are equal and to `rt:equal-distinct` otherwise. `rt:equal-second` moves the deferred pair from X2 and X3 into X0 and X1. `rt:equal-cons` replaces two cons words by their cell addresses. Each block keeps SP and mapped memory and changes no other general register. |
| `store-views` | `p6-published-view-after-disjoint-pair-store`, `p6-object-descriptors-after-disjoint-pair-store` | A store of two words outside the contents of every published object leaves the view of every word, and the size and symbol status of every object, unchanged. |
| `store-views` | `p6-stack-store-avoids-published-objects`, `p6-stack-store-preserves-published-views` | Under the heap invariant, a 16-byte span inside the value-stack reservation or the machine-stack reservation avoids the contents of every published object, so a pair store there preserves every published view. |
| `store-frame` | `p6-pair-store-preserves-layout`, `p6-stack-store-preserves-heap` | A store of two words to a 16-byte span inside the value-stack or machine-stack reservation preserves the heap layout. When the span also avoids the live part of the value stack, from its base to its top, the heap invariant `proof-heap-p` still holds afterwards with the same published objects. |
| `store-frame` | `p6-stack-store-preserves-prefix`, `p6-stack-store-preserves-fixed-heap` | Such a store leaves the views of the value stack below any top unchanged when the span avoids that prefix. At a nonzero address it satisfies `proof-fixed-heap-p`: the regions, replies, allocation pointers, heap memory and external mappings stay fixed. |
| `boxed-scratch` | `p6-numeric-save-preserves-heap`, `p6-numeric-save-preserves-argument-view` | The save of X29 and X30 below SP made by a numeric projection, with room in the machine-stack reservation, satisfies `proof-preserved-heap-p` without interning, and keeps the view of the argument in X0. |
| `boxed-scratch` | `p6-boxed-numeric-projections-runtime-contract-with-room` | With the placement and load-permission premises of `p6-boxed-numeric-pre-p` and room for the save, `NUMERATOR`, `DENOMINATOR`, `REALPART` and `IMAGPART` satisfy the runtime contract on header, cons and character arguments. The heap invariant, root views and argument view across the save are proved here rather than assumed. |
| `numeric-contract` | `p6-numeric-projections-runtime-contract` | `NUMERATOR`, `DENOMINATOR`, `REALPART` and `IMAGPART` satisfy the runtime contract on every represented argument. The checked path is the immediate one for an odd word and the boxed one otherwise. `p6-numeric-projection-pre-p` collects the placement premises of the selected path and, for an even word, room for the save. |
| `growth-example` | `p6-growth-overflow-example` | A concrete state, outside the heap invariant only by its reservation bound, in which `rt:ensure-stack` returns but its result does not satisfy `proof-grow-return-p`. The section below explains it. |

`BAD-ATOM<=` gives NIL in the ACL2 Core evaluator of
`compiler/model/core.lisp`, as the [language
specification](../../../../spec/language.md), section 4, says ACL2 Core
computes, and the compiler entry gives NIL without reading the arguments.
The command
`grep -n 'bad-atom<=' compiler/model/core.lisp` shows the evaluator clause.

## Stack growth near the top of the address space

The comment before `rt:grow` in `compiler/single/runtime.lisp` says that growth
uses the larger of the required size and twice the current size, capped
at the end of the reservation. The foundations state the same result as
`proof-grow-limit`. The routine computes the doubled limit, the stack
base plus twice the current size, in 64-bit arithmetic. Were that sum to
reach `2^64` it would wrap to a small number, and the routine would
install the required address as the new limit instead of the end of the
reservation.

The heap invariant `proof-heap-layout-p` therefore requires the stack
base plus twice `*proof-value-reservation*` to be at most `2^64`. The
doubled limit is computed only when the current limit lies below the end
of the reservation, so under that bound it stays below `2^64`.
`growth-example` builds a state whose reservation ends at
`#xfffffffffffff000`, with a current limit three quarters of the way
through the reservation and a required address 16 bytes above it. The
state fails `proof-heap-p` by that bound alone. The checked run of
`rt:ensure-stack` reaches the return address within 13 steps with the
limit `#xffffffffeffff010`, while `proof-grow-limit` gives
`#xfffffffffffff000`, and `proof-grow-return-p` fails. An `assert-event`
in the book checks these values whenever the book is certified.

## Open goals

- Discharge the placement premises for the runtime in a loaded executable,
  including separation of the selected instruction addresses from the
  return address. The premises of `p6-boxed-numeric-pre-p` also include
  read permission for the argument's header and projected field, which
  the heap invariant should supply as `mapped-data` does for the leaf
  routines.
- Prove the full distinct-word `EQUAL` runtime contract by composing the
  branch blocks and loops. The entry block that saves X25 and X30 and
  branches to `rt:equal-distinct` has no checked-path theorem yet.
  Relate the machine's pending comparisons to the abstract work measure
  and prove preservation of incoming roots across deferred writes;
  `store-frame` supplies the heap invariant across each pair store.
  The proof must use
  `proof-grow-return-p` at `rt:ensure-stack`, which first needs one of
  the changes described in the previous section, and must account for
  the stack-limit stop and the vector case for internal views.

## Certification

Run from the repository root with ACL2 8.7 available as `acl2`.

```sh
SBCL_USER_ARGS='--dynamic-space-size 2500' sh compiler/single/proofs/certify.sh --foundations
sh compiler/single/proofs/primitives/certify.sh
```

On 2026-11-26, ACL2 8.7 certified the 21 compiler, model and
foundation books with the first command, in 27 seconds, which printed
`Compiler proof foundations certified.` It then certified all 34 books
in this directory in logic mode with the second command, in 256 seconds
while five other packages were certified beside it. The package command
printed `Certified` with each book's source path and exited with status
0. This run checks the theorem statements above and the values that
`growth-example` asserts.
