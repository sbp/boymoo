# Fraction and complex arithmetic

The books relate the compiler's numeric runtime in `compiler/runtime.lisp`
to the ACL2 Core operations in `compiler/model/core.lisp`. A *view* is
the value obtained by interpreting a tagged word with the published
object map. That map records each published object's address, kind and
rank. References from an object lead to lower ranks. A *cutpoint* is an
address at which checked execution stops before the next instruction.
An *initialized prefix* is the sequence of represented values from the
value-stack base to a specified top.

The public return contracts are instances of `proof-runtime-return-p`.
They relate a completed machine segment to the source result, a valid
heap, the caller's initialized stack prefix and the registers that its
callee must preserve. The checked traces identify the instructions and
lower-level calls that constitute the segment. Internal routines use
`proof-datum-return-p` to state the same obligations for a specified
result datum and a specified set of registers they may change.

## Canonical values and boxing

The quotient of a reduced pair has an integer numerator and a positive
denominator, and its ACL2 numerator and denominator recover the pair.
A denominator of one yields an integer. A complex object stores two
rational fields and has a nonzero imaginary part.

| Theorem | Result |
|---|---|
| `proof-number-reduction` | The GCD of an integer numerator and a positive denominator gives exact quotients that form the reduced pair for the original rational. |
| `proof-number-negated-parts-are-reduced` | Negating the numerator preserves reduction and the positive denominator. |
| `proof-number-inverted-parts-are-reduced` | For a nonzero reduced numerator, taking its magnitude as the denominator and applying its sign to the old denominator gives a reduced reciprocal. |
| `proof-number-fraction-fields` | The two field words of a published fraction represent its ACL2 numerator and denominator. |
| `proof-number-complex-fields` | The two field words of a published complex object represent its ACL2 real and imaginary parts. |
| `proof-number-q-normalize-dispatch-by-value` | The checked `rt:q-normalize` prefix selects the zero, identity or reduction path from the integer numerator and positive denominator. |
| `proof-number-q-normalize-trivial-return` | The zero and denominator-one paths return the canonical quotient to the caller. |
| `proof-number-q-normalize-reduction-return` | With the generated reduction formula's checked trace and a GCD witness, the reduction path returns the canonical quotient. |
| `proof-number-q-normalize-trivial-datum-return`, `proof-number-q-normalize-reduction-datum-return` | The zero, denominator-one and reduction paths satisfy the datum return contract for the quotient with a positive denominator. The reduction path uses the checked formula and GCD witness. |
| `proof-number-invert-dispatch` | The raw-parts reciprocal sends zero to the zero return, a negative numerator to sign adjustment, and a positive numerator to the rational box with the operands exchanged. |
| `proof-number-zero-inversion-return`, `proof-number-negative-inversion-return` | The zero path returns zero. The negative path returns the reciprocal given the checked trace of its sign-adjustment formula. |
| `proof-number-positive-inversion-passes-reduced-parts` | The positive path passes represented, exchanged fields that satisfy the reduced-pair premise of rational boxing. |
| `proof-number-box-select-by-value` | Rational boxing skips allocation for denominator one. Complex boxing skips allocation for imaginary part zero. |
| `proof-number-box-collapse-return` | Both allocation-free boxing paths return the first operand as the mathematical result. |
| `proof-number-box-calls-reserve` | The shared boxing block saves the header and link, puts 24 in X2 and reaches `rt:z-reserve`. |
| `proof-number-box-publish-writes-only-three-fields` | The publication block changes memory by writing the header and two field words. |
| `proof-number-reserved-span-avoids-old-headers` | The allocator's reserved span and a valid object map imply that the three stores avoid the existing headers and payloads. |
| `proof-number-box-publishes-reserved-value` | The publication block restores the link and stack pointer and produces the canonical value with the new object in the map. Field values may themselves use heap objects. |
| `proof-number-box-fields-return` | Given the reserve call's checked return and postcondition, the saves and publication form a single segment from the shared boxing block to the original return address. |
| `proof-number-box-allocated-return` | The allocation paths of `rt:q-box` and `rt:c-box` return their canonical values using the checked reservation and publication sequence. |
| `proof-number-box-collapsed-datum-return` | The two allocation-free boxing paths satisfy the datum return contract for the original numerator or real part. |
| `proof-number-box-publication-preserves-heap` | The three checked stores install a fresh numeric record with valid fields and preserve old views, the initialized stack, static data and the dynamic symbol table. |
| `proof-number-box-fields-datum-return`, `proof-number-box-allocated-datum-return` | Given the checked reservation return, the shared allocator caller and both boxing entries satisfy the datum return contract with a valid extended object map. |
| `proof-number-positive-inversion-returns-through-box` | The positive-numerator reciprocal passes the exchanged reduced fields to the rational box and returns their quotient. |
| `proof-number-zero-inversion-datum-return`, `proof-number-negative-inversion-datum-return`, `proof-number-positive-inversion-datum-return` | The three raw reciprocal branches satisfy the datum return contract. The zero branch returns zero, the negative branch uses the checked sign-adjustment formula, and the positive branch uses the checked rational box with the exchanged reduced fields. |
| `proof-number-rational-reciprocal-datum-return` | The generated rational reciprocal meets the datum return contract for the reciprocal of its represented rational input, including zero. |

`proof-number-box-select-decoding`, `proof-number-box-fields-decoding`,
`proof-number-invert-decoding` and `proof-number-q-normalize-decoding`
check these blocks against the compiler's assembled instruction forms.
The machine execution theorems require the decoded instructions and
their accesses to be admitted by the checked machine at the named
addresses.

## Generated formulas

`proof-number-formulas-describe-runtime-code` checks that regenerating
the extracted formula table gives the same runtime code.
`proof-number-generated-formula-decoding` checks the decoding of each
prologue, argument store, argument load, call, spill and return.
`proof-number-generated-formulas-use-initialized-slots` establishes
that each call reads original arguments or results of earlier calls.

Each of the following theorems gives both the mathematical result and
the domain of every call in the extracted formula. For `rt:q-reduce`,
`proof-gcd-p` supplies the positive greatest common divisor of the
integer fields, and `proof-exact-quotient-p` checks both divisions.
`rt:q-box` and `rt:q-invert-parts` take two represented integers that
are already the reduced numerator and positive denominator of the
quotient. `rt:q-normalize` takes a represented integer numerator and
represented positive denominator and reduces them when required.

| Theorem | Result |
|---|---|
| `proof-number-q-reduce-formula` | The two exact integer quotients give the reduced pair for the original rational. |
| `proof-number-q-add-formula` | Cross multiplication and normalization give the sum of two rationals. |
| `proof-number-q-multiply-formula` | Multiplying the numerators and denominators and normalizing gives the product of two rationals. |
| `proof-number-q-negate-formula` | Negating the numerator with the denominator unchanged gives the rational negation. |
| `proof-number-q-reciprocal-formula` | Inverting the reduced parts gives the reciprocal of a rational, with zero mapped to zero. |
| `proof-number-q-invert-negative-formula` | Negating both operands while exchanging them gives a reduced reciprocal with positive denominator for a negative numerator. |
| `proof-number-q-compare-products-formula` | Comparing cross products orders rationals with positive denominators. |
| `proof-number-c-add-formula` | Adding real and imaginary parts separately gives the complex sum. |
| `proof-number-c-multiply-formula` | The real part is the difference of the real and imaginary products. The imaginary part is the sum of the cross products. |
| `proof-number-c-negate-formula` | Negating both parts gives the complex negation. |
| `proof-number-c-reciprocal-formula` | Multiplying the conjugate by the reciprocal of the sum of the squared parts gives the reciprocal, with zero mapped to zero. |
| `proof-number-c-compare-formula` | The real parts determine the order when unequal. Equal real parts leave the order to the imaginary parts. |

`proof-number-frame-p` describes the initialized value stack from the
formula's first slot through its current top. The slot views record ACL2
values, so a collector may change a word while preserving the value it
represents.

| Theorem | Result |
|---|---|
| `proof-number-formula-calls-growth` | The prologue saves the frame register and link and passes the required value-stack limit to `rt:ensure-stack`. |
| `proof-number-formula-writes-arguments` | The argument stores populate the first one or two words and advance the value-stack top by their size. |
| `proof-number-formula-entry-initializes-frame` | With a checked growth return and the argument stores' locality premises, the generated entry establishes the initialized frame. |
| `proof-number-frame-across-datum-return`, `proof-number-frame-across-runtime-return`, `proof-number-frame-across-reserve-return`, `proof-number-frame-across-grow-return` | Each stated callee contract preserves the views of the initialized formula slots. |
| `proof-number-frame-slot-value`, `proof-number-formula-passes-slot-values` | A slot read and a generated load-and-call sequence obtain the indexed ACL2 operands. |
| `proof-number-formula-spill-extends-frame` | A store and top increment add the returned value while keeping the previous slots, given the spill's memory locality conditions. |
| `proof-number-formula-body-follows-evaluation` | A trace of the named callee returns and checked spills executes the generated formula body and returns its mathematical evaluation. The theorem uses the frame invariant at the entry and proves it across each call and spill. |
| `proof-number-formula-restores-frame` | The epilogue restores the caller's frame register, stack pointers and link while retaining the numerical result in X0. |
| `proof-number-generated-formula-return` | The checked entry, calls, spills and epilogue return the result of the named formula. The hypotheses state the lower-level returns and the stores' locality conditions. |
| `proof-number-formula-body-preserves-machine-save` | The checked calls and spills preserve both words of the formula's machine-stack save. |
| `proof-number-generated-formula-return-with-saved-link` | The formula returns using the link and frame register saved by its prologue and restores the machine stack. |
| `proof-number-formula-growth-preserves-heap-and-register-frame` | The checked prologue and growth return preserve the heap and reach the stores with the caller's value-stack top in X19. |
| `proof-number-formula-entry-preserves-heap-and-register-frame` | The growth return and stores establish the initialized formula slots with a valid heap and the stated register frame. |
| `proof-number-formula-body-preserves-heap-and-register-frame` | The calls and spills maintain a valid heap throughout the formula body and keep the caller's initialized prefix and dynamic symbols. |
| `proof-number-formula-epilogue-preserves-heap-window` | The epilogue drops the temporary value slots and restores the machine stack while keeping the retained prefix and heap. |
| `proof-number-generated-formula-datum-return` | The trace of a named formula satisfies the datum return contract, including its mathematical result, heap, original value-stack top and caller's preserved registers. |
| `proof-number-generated-formula-return-from-checked-stores` | With machine-stack room, checked argument and spill instructions within committed capacity establish their store effects and the full generated-formula return contract. The trace supplies the live operands after growth and the named callees' checked returns. |

## Dispatch and completion

| Theorem | Result |
|---|---|
| `proof-number-classifier-returns-datum-class` | A published value is classified as integer, fraction, complex rational or other. |
| `proof-number-public-value-completions` | The six source primitives agree with the stated total operations. Arithmetic and order fix nonnumbers to zero, the reciprocal of zero is zero, and `COMPLEX` fixes each nonrational component to zero. |
| `proof-number-types-return-completed-values` | The checked completion blocks leave the fixed operands in registers. The arithmetic block also returns the maximum numeric class. |
| `proof-number-types-return-or-fallthrough` | Both classifier calls and completion blocks restore the machine stack and saved registers. They return from `rt:n-types` or fall through to `rt:c-box`, with the completed operand views. |
| `proof-number-complex-collapsed-return`, `proof-number-complex-allocated-return` | The full checked `COMPLEX` paths return its rational or complex value after operand completion. The allocation path uses the reserve return contract. |
| `proof-number-add-dispatch-by-value`, `proof-number-multiply-dispatch-by-value` | The checked dispatch after operand completion selects the identity, zero, integer, rational or complex path as applicable. |
| `proof-number-negation-dispatch-by-value`, `proof-number-reciprocal-dispatch-by-value` | The checked dispatch selects zero for a nonnumber and the prescribed integer, rational or complex helper for a number. |
| `proof-number-rational-comparison-dispatch-by-value` | The checked rational comparison dispatch selects integer comparison or cross-product comparison. |
| `proof-number-less-calls-comparator`, `proof-number-less-uses-order-sign` | Numeric less-than calls the rational or complex comparator and uses the sign of the returned order to select the Boolean result. |
| `proof-number-first-order-returns-value` | The complex comparison continuation returns the first nonzero order, with the real comparison supplied first. |
| `proof-number-leaf-returns-word` | The shared returns produce the unchanged operand, second operand, tagged zero, true or nil. |
| `proof-number-public-tag-gate` | The decoded public tag tests select the immediate path exactly when all operands carry immediate integer tags. |
| `proof-number-immediate-add-negate-returns-or-delegates` | For immediate inputs, addition and negation either return the exact tagged result or send the unchanged operands to the integer helper on signed overflow. |
| `proof-number-execute-arithmetic-right`, `proof-number-multiply-high-tests-signed-range` | The two arithmetic right shifts implement signed division by a power of two with rounding down. The signed high word equals the low word's sign extension exactly when the product fits a signed word. |
| `proof-number-immediate-multiply-returns-or-delegates` | The multiply instructions return the exact tagged product when it fits and pass the unchanged operands to `rt:z-multiply-op` otherwise. |
| `proof-number-immediate-reciprocal-returns-or-delegates` | The immediate reciprocal returns its operand for minus one, zero and one. Other immediate integers go to `rt:q-reciprocal`. |
| `proof-number-immediate-less-returns-word` | With two immediate integers, the public comparison returns the true or nil word according to signed integer order. |
| `proof-number-dispatched-formula-returns-source-value` | From the completed and classified operands, a selected rational or complex formula for the four arithmetic primitives returns the ACL2 Core result. |
| `proof-number-dispatched-leaf-returns-source-value` | From the same dispatch boundary, a selected zero or identity return produces the ACL2 Core result without entering a formula. |
| `proof-number-public-immediate-runtime-return` | With immediate operands and a result returned on the immediate path, the public entry meets the runtime return contract through its tag tests and body. |
| `proof-number-immediate-tag-agrees-with-datum` | A represented value uses an immediate tag exactly when the value fits the immediate integer representation. |
| `proof-number-public-delegated-immediate-runtime-return` | The immediate overflow and nontrivial reciprocal branches pass the original operands to the selected helper and preserve the runtime contract when that helper returns. |
| `proof-number-public-immediate-reciprocal-through-formula` | The delegated immediate reciprocal satisfies the public `UNARY-/` return contract using the checked trace of the rational reciprocal formula. |
| `proof-number-complex-runtime-return` | The public `COMPLEX` entry meets the runtime return contract with either a collapsed rational result or a newly published complex object. The completed imaginary part determines which branch runs. |
| `proof-number-less-executes-selected-comparison`, `proof-number-general-less-returns-boolean` | The comparator's checked return selects the true or nil word, and the general routine restores the saved machine-stack state. |
| `proof-number-public-general-less-runtime-return` | The public `<` general path meets the runtime return contract through the tag gate, completion, selected comparator and Boolean tail. |
| `proof-number-rational-comparison-returns-through-callee` | Rational comparison runs through integer order or cross-product order using the stated callee contract. |
| `proof-number-first-order-datum-return`, `proof-number-complex-order-datum-return` | The first-order helper returns the second order when the first is zero. The generated complex comparison applies that rule to the real and imaginary orders and satisfies the datum return contract. |
| `proof-number-rational-cross-products-datum-return`, `proof-number-rational-comparison-datum-return` | Cross-product comparison satisfies the datum return contract for rational order. The rational wrapper completes the operands and preserves the caller's frame through its selected comparator. |
| `proof-number-rational-comparison-checked-datum-return` | Rational order uses the checked cross-product formula for fractional operands and the lower-level integer comparison contract for integer operands. |
| `proof-number-binary-arithmetic-wrapper-keeps-dispatch-context`, `proof-number-unary-arithmetic-wrapper-keeps-dispatch-context` | The general arithmetic wrappers restore the stack and saved registers and reach dispatch with the required operands and heap frame. |
| `proof-number-arithmetic-decision-keeps-dispatch-context`, `proof-number-arithmetic-decision-passes-operand` | The checked decisions reach the selected helper with the operands, heap, register frame and caller's link. |
| `proof-number-selected-integer-helper-domain` | The integer helpers selected by addition, multiplication and negation receive integer operands and have an integer source result. |
| `proof-number-arithmetic-dispatch-returns-through-helper` | The checked decision and selected helper's checked datum return together meet the runtime return contract at the dispatch boundary. |
| `proof-number-dispatched-leaf-runtime-return`, `proof-number-dispatched-formula-runtime-return` | The checked leaf returns and generated arithmetic formulas establish the selected helper's runtime return contract. |
| `proof-number-public-general-arithmetic-checked-return` | The general arithmetic entry uses the checked zero, identity, formula or integer helper selected by its decoded instructions. |
| `proof-number-public-arithmetic-runtime-return` | The public `BINARY-+`, `BINARY-*`, `UNARY--` and `UNARY-/` contracts cover successful immediate, delegated and general paths with the stated traces. |
| `proof-number-public-less-runtime-return` | The public `<` contract covers immediate integer order and the general path through the selected comparator. |
| `proof-number-public-general-less-checked-runtime-return` | The general path of public `<` uses the checked rational or complex comparison trace selected by the runtime. |

The mathematical and machine-level statements use the same source and
runtime names. The machine statements about calls distinguish the
checked instructions that reach a callee from its subsequently assumed
return contract.

## Memory and stack frames

A *footprint* is the integer interval of byte addresses in which a
checked store may change memory. The memory image is a sparse list of
address and byte pairs.

| Theorem | Result |
|---|---|
| `proof-number-load-linux-preserves-byte-keys`, `proof-number-step-preserves-byte-keys` | The loader and model transitions preserve unsigned byte-address keys from a well-formed initial memory. |
| `proof-number-view-kept-with-object-memory`, `proof-number-stack-views-kept-with-object-memory` | A datum and the value-stack slots retain their views when the referenced objects' memory and map records agree. |
| `proof-number-disjoint-footprint-keeps-old-values`, `proof-number-disjoint-footprint-keeps-prefix` | A bounded disjoint write keeps old represented values and the initialized stack prefix. |
| `proof-number-published-record-extends-map` | Adding a valid fresh numeric record keeps the map valid. |
| `proof-number-heap-frames-compose`, `proof-number-preserved-heaps-compose` | Under their range and byte-key conditions, consecutive frames keep the caller's static memory, machine-stack range, value prefix and dynamic table. |
| `proof-number-static-block-kept`, `proof-number-external-chain-and-accounting-kept` | A local write with protected records keeps the valid static block and the external object chain with its byte accounting. |
| `proof-number-same-top-local-write-preserves-heap`, `proof-number-local-write-keeps-heap-with-initialized-stack` | The local write maintains heap validity when the new object map and initialized stack satisfy the stated conditions. |
| `proof-number-machine-save-preserves-heap`, `proof-number-unwritten-machine-frame-preserves-heap` | A disjoint machine-stack save preserves the heap. A stack-pointer change within the reservation also preserves it when memory and the heap coordinates agree. |
| `proof-number-stack-footprint-avoids-objects`, `proof-number-heap-gives-machine-save-locality` | A valid heap separates either stack reservation from all published objects, including externally mapped strings. A bounded machine-stack save inherits this separation. |
| `proof-number-heap-gives-value-append-locality`, `proof-number-checked-argument-store-from-heap`, `proof-number-checked-spill-store-from-heap` | A bounded append within the committed value stack has disjoint storage. The checked argument and spill instructions preserve old views and keep the appended values represented. |
| `proof-number-argument-trace-from-disjoint-store`, `proof-number-spill-trace-from-disjoint-store` | Checked stores with bounded disjoint storage establish the locality conditions for pushing arguments and spilling results. |
| `proof-number-type-completion-preserves-heap`, `proof-number-type-completion-keeps-save-interval` | The numeric completion's save and return preserve the heap and keep the save interval available afterward. |
| `proof-number-value-append-preserves-heap`, `proof-number-value-stack-drop-keeps-heap-window` | Appending initialized slots and dropping temporary slots keep the applicable value prefix and heap frame. |
| `proof-number-register-only-execution-preserves-heap`, `proof-number-register-frames-extend-and-compose` | Under the stated clobber conditions, the listed register-only sequences preserve the heap, and successive register frames can be composed. |

## Resource stops

The resource observation is exit status 3 with empty standard output.
The stop traces supply the checked lower-level run and the conditions
that prevent an earlier return to the caller.

| Theorem | Result |
|---|---|
| `proof-number-resource-return-with-outer-cut` | The same checked resource stop holds with the caller's outer cutpoint. |
| `proof-number-formula-propagates-stack-exhaustion` | The formula prologue requests the calculated value-stack top and propagates an observed growth stop when the demand exceeds the reservation. |
| `proof-number-formula-call-propagates-resource-stop` | A generated call loads the represented operands from its initialized slots and propagates a checked resource stop from the callee. |
| `proof-number-box-propagates-reservation-stop`, `proof-number-complex-propagates-reservation-stop` | Boxing requests 24 bytes and propagates a checked reservation stop through the nonzero-imaginary-part path of `COMPLEX`. |
| `proof-number-public-immediate-propagates-helper-stop`, `proof-number-public-general-arithmetic-propagates-helper-stop` | The four public arithmetic entries propagate a checked resource stop from the helper reached through the immediate or general path. |
| `proof-number-general-less-propagates-comparator-stop`, `proof-number-public-less-propagates-comparator-stop` | Both comparison entries propagate a checked resource stop from the selected comparator. |

## Open obligations

Each trace supplies decoded instruction placement, access checks and
conditions on cutpoints. The assembler and loader need a correspondence
theorem that gives those instruction and address facts for the loaded
executable. The integer, exact quotient, GCD, allocator and growth calls
use their stated return conditions. Formula traces also supply the
checked returns of their named projection, arithmetic and raw-field
calls. The helper theorems give separate proofs for the stated
numeric paths. Constructing every nested trace from the loaded image
and proving that execution reaches either a normal return or a resource
stop remain open. The resource proofs propagate checked lower-level
stops. Machine-stack exhaustion remains open.

The composed returns use unsigned byte keys at entry and derive them at
subsequent checked states. A reachable-world invariant in the foundations
established from a loader with canonical initial byte keys would supply
the entry condition. A call-site invariant giving sufficient aligned
machine-stack headroom, with a checked stop on exhaustion, would supply
the numeric space bounds for the saves. A growth contract that
carries the live register views through a fixed heap would supply the
operand views after a successful growth call. A lower-level frame that
retains the required committed value-stack limit would supply the
capacity conditions for subsequent spills.

## Certification

Run these commands from the repository root with ACL2 8.7 on `PATH`.

```sh
SBCL_USER_ARGS='--dynamic-space-size 2500' sh compiler/proofs/certify.sh --foundations
SBCL_USER_ARGS='--dynamic-space-size 2500' sh compiler/proofs/numbers/certify.sh
sh compiler/test-numbers.sh
```

The package command checks each book in logic mode with the admission
of skipped proofs, axioms and trust tags disabled. It stages the books
and their certificate output under `build/compiler/proofs/numbers/`.

On 2026-11-26, ACL2 8.7 certified the following books. The elapsed times
are wall-clock measurements. Resident sizes are peak child-process
measurements in bytes.

| Command | Result | Elapsed | Peak resident size |
|---|---|---:|---:|
| Foundations command above | Certified 21 books and printed `Compiler proof foundations certified.` | 55.30 s | 496,877,568 |
| `sh compiler/proofs/numbers/certify.sh` | Printed one `Certified` line for each of the 74 books, ending with `Certified compiler/proofs/numbers/formula-storage.lisp.` | 668.67 s | 566,771,712 |

On the same date, `sh compiler/test-numbers.sh` printed
`Numeric primitives and jets agree on 16281 bytes of results.` It took
23.27 seconds and had a peak child-process resident size of 40,812,544
bytes.
