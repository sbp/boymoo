# Integer division and greatest common divisor

The arithmetic uses radix `B = 2^32`. A limb is an integer in
`[0, B)` stored in an eight-byte word. Lists of limbs put the least
significant limb first. A normalized magnitude has a positive
most significant limb, or an empty limb list for zero. A window
in long division consists of as many low limbs as the divisor has,
together with one more limb at the high end.

## Arithmetic results

| Theorem | Statement |
| --- | --- |
| `division-floor-bounds`, `division-mod-bounds`, and `division-quotient-unique` | Natural division by a positive divisor has a unique quotient and a remainder in the half-open interval bounded by zero and the divisor. |
| `division-signed-floor-bounds`, `division-mask-is-remainder`, and `division-a64-unsigned-is-remainder` | Floor division has its usual bounds on signed inputs, and retaining the low bits of a signed integer gives its remainder modulo the corresponding power of two. |
| `division-shift-joins-carry`, `division-asr-decodes-immediate`, and `division-lsl-and-add-encode-immediate` | The shifted digit and incoming carry occupy disjoint fields. The bitfield used for arithmetic right shift decodes an immediate integer, and the bitfield used for left shift followed by an addition of one encodes it. |
| `division-one-limb-step-correct` and `division-one-limb-loop-correct` | The one-limb loop combines the incoming remainder and next limb in a single 64-bit word. Each iteration writes a radix-`B` quotient digit and preserves the remainder bound. The loop reconstructs the entire dividend. |
| `division-one-limb-result-correct` | Trimming the quotient and using an empty limb list for a zero remainder gives normalized magnitudes with `a = b*q + r` and `0 <= r < b`. |
| `division-estimate-test-correct` and `division-correct-estimate-maximal` | The estimate test compares the product of the current guess and the leading two divisor limbs with the leading three dividend limbs. The loop returns the greatest feasible guess at or below its initial guess. |
| `division-estimate-at-most-two-corrections`, `division-estimate-words-fit`, and `division-window-estimate-bounds` | The estimate needs at most two decrements. Each compared quantity fits a word on the branch that computes it. For the corrected estimate `e`, dividend window `u`, and normalized divisor `v`, the bounds are `(e-1)*v < u < (e+1)*v`. |
| `division-clz-count-in-model`, `division-clz-shift-bounds`, and `division-normalized-leading-digit` | Subtracting 32 from the modeled 64-bit CLZ result gives a shift in `[0, 31]` for a positive limb. The shifted leading limb, including the incoming carry, lies in `[B/2, B)`. |
| `division-left-shift-limbs-correct` and `division-left-shift-normalizes-divisor` | The left shift represents multiplication by its scale. The normalized divisor has a leading limb in `[B/2, B)` and produces zero carry above it. |
| `division-right-shift-digit-correct` and `division-undo-normalization` | The low limb of a shifted two-limb word is the corresponding division digit. A common positive scale preserves the quotient and scales the remainder by that same factor, so dividing the scaled remainder by the scale is exact. |
| `division-subtract-product-word`, `division-subtract-limbs-correct`, and `division-add-back-limbs-correct` | The multiply-and-subtract accumulator fits in a word. Its carry is at most the estimate. The add-back carry is at most one. Both loops preserve the stated positional values of their written limbs and final carry. |
| `division-subtract-window-correct`, `division-add-back-window-correct`, and `division-normalized-window-iteration` | The high-limb borrow detects a negative window after subtraction. Decrementing the estimate and adding back the divisor in that case gives a quotient digit and a remainder below the divisor with zero in the extra high limb. The window theorem assumes the leading fields represent the corresponding prefixes of the dividend and divisor. |
| `division-normalized-loop-correct` and `division-normalized-loop-gives-unscaled-result` | The recurrence over normalized windows reconstructs the normalized dividend. When the two inputs represent magnitudes multiplied by the same scale, the trimmed quotient and the exact unscaled remainder reconstruct the original dividend. |
| `division-view-magnitude-and-count` and `division-shorten-dividend` | The integer-view header yields the byte count used by division and its limbs represent the absolute value. A dividend with fewer significant limbs than the divisor has quotient zero and is its own remainder. |
| `division-normalized-window-ranges`, `division-one-limb-ranges`, `division-distinct-buffers`, and `division-covered-subspan` | The quotient store, remainder window and normalized divisor scratch fit the five-buffer reservation at their respective offsets. Distinct buffer slots have disjoint spans. A subspan of a mapped span has the same access permission. |
| `division-exact-quotient-sign`, `division-exact-divisor-remainder-zero`, and `division-exact-immediate-fits` | Restoring the dividend's sign to a magnitude quotient gives the signed exact quotient. An exact divisor gives zero remainder, and division of an immediate integer by a positive exact divisor has an immediate quotient. |
| `division-euclid-remainder-decreases`, `division-euclid-witness`, `division-euclid-gcd-contract`, and `division-euclid-zero-first` | A Euclidean step strictly decreases the positive second magnitude. The recurrence gives a common divisor and integer coefficients expressing it as a combination of the operands. Its value satisfies `proof-gcd-p`, including for a zero first operand and positive second operand. |

## Checked instruction segments

The instruction results use the foundation machine. A cut is a
designated program-counter value at which a run stops. The prefix
and segment predicates check decoded instructions and access
permissions and exclude an earlier cut. The branch theorems below
make the relevant placement, access and frame premises explicit.

| Theorem | Statement |
| --- | --- |
| `division-instruction-sequence-runs-to-cut` and `division-segment-from-cut-free-prefix` | A checked sequence runs to its first designated cut. A prefix that avoids the cuts can be joined to a checked suffix. |
| `division-linked-image-instructions-at-offset` | An aligned instruction slice matching the assembled fragments is present at its loaded address whenever the linked-image predicate holds. |
| `division-compile-items-has-runtime-prefix` and `division-layout-proceeds-from-runtime-to-program` | The compiler emits the system and runtime items ahead of generated functions and data. The assembler can lay out the generated suffix starting from the state after successful prefix layout. |
| `division-runtime-example-words-agree-on-targets` | The division runtime in the example program decodes to the same instructions in the Linux and macOS assembled images. |
| `division-instructions-at-after-disjoint-write` and `division-span-agreement-covers-byte` | A disjoint store preserves instruction placement when regions agree. Span agreement preserves the bytes of the span. |
| `division-divide-dispatch-runs` | The divider saves its frame, reads the two limb counts, and reaches the short, one-limb, or multi-limb branch. |
| `division-one-limb-instructions-are-emitted` and `division-one-limb-iteration-runs` | The example image emits the decoded one-limb loop. Each checked iteration stores a quotient limb, updates the remainder and takes the appropriate branch. |
| `division-one-limb-checked-loop-result` and `division-divide-one-writes-quotient-and-remainder` | The descending loop reads the dividend and writes the quotient at seven steps per limb. The one-limb branch also stores the remainder before normalization. |
| `division-copy-call-returns-view` and `division-short-prepares-unsigned-results` | The checked copy call reproduces an integer view, including its header and sign. The short branch prepares an empty quotient and the dividend magnitude as remainder. |
| `division-divide-normalize-and-return` | The two normalization calls and restoring epilogue return normalized views when the normalization contracts, saved frame and stable quotient span hold. |
| `division-normalizer-trims-limb-list` and `division-normalizer-returns-unsigned-view` | The checked `rt:z-normalize` call removes leading zero limbs, writes the normalized header and sign, and returns through the saved link. Its exact memory effect is the two header-word stores. |
| `division-one-limb-entry-to-return` and `division-short-entry-to-return` | From the divider entry, these cases return normalized floor and remainder views at the output addresses and restore SP and the saved registers, under the stated normalization and memory premises. |
| `division-chooses-and-saves-clz-shift` and `division-undo-normalization-setup-runs` | The checked code reads the leading divisor limb, saves its shift and the dividend length, and restores the shift and computes the quotient count after traversal. |
| `division-left-shift-loop-writes-scaled-value` and `division-left-shift-call-returns-shifted-limbs` | The checked left shift writes the scaled limbs and computes the high carry. The call includes its initialization and return. |
| `division-right-shift-loop-writes-unscaled-value` and `division-right-shift-preserves-disjoint-limbs` | The right shift writes the remainder divided by the scale, rounded down, and preserves disjoint limb reads. |
| `division-estimate-loop-from-head` | The checked estimate reaches subtraction with the corrected estimate in at most 24 instructions. |
| `division-window-loop-correct` and `division-window-correction-reaches-store` | The checked low-limb loops perform subtraction and add-back. The high limbs and the borrow select the adjusted result at the quotient store. |
| `division-one-normalized-position-executes` and `division-position-from-memory` | An emitted long-division position reads its window, estimates and corrects the quotient limb, stores the digit and remainder, clears the high limb, and reaches the next position or falls through. The leading fields follow from the buffer layout. |
| `division-position-preserves-disjoint-limbs` and `division-long-run-preserves-external-limbs` | The position preserves limb reads disjoint from its window and quotient slot. The traversal preserves limb reads outside its two working spans. |
| `division-long-traversal-writes-quotient-and-scaled-remainder` | With checked conditions at each position, the traversal reaches its fall-through and the quotient and scaled remainder reconstructed from memory satisfy the division identity and remainder bound. |
| `division-first-scaled-position-window-bound`, `division-next-position-window-bound`, and `division-long-run-ready-after-scaling` | Scaling establishes the first numerical window bound. Each emitted position computes a remainder that establishes the bound for the next position when the next low limb fits the radix. The traversal uses these bounds with the checked layout and access conditions. |
| `division-long-scale-prepares-operands` and `division-unscales-remainder-and-keeps-quotient` | The checked scale prefix selects the shift, scales both buffers and enters the first long-division position. The unscale segment divides the stored remainder by the scale and preserves the quotient. |
| `division-long-normalized-entry-to-return` and `division-multi-limb-entry-to-return` | The long-division traversal and remaining calls return the unscaled result. The multi-limb theorem starts at the divider entry and includes dispatch and scaling. |
| `division-unsigned-entry-to-return` | All three paths of `rt:z-divide` divide the magnitudes of two integer views with a nonzero divisor. They return normalized quotient and remainder views at the supplied output addresses. X0 points to the remainder. SP and X19–X22 and X29–X30 are restored. |
| `division-public-dispatch-runs` | The public entries use the tags and unit tests to select the unit, immediate, or boxed path. The boxed path receives the operation selector. |
| `division-quotient-by-one-returns` and `division-public-immediate-quotient-returns` | Quotient by one returns the dividend word. The exact quotient of two immediate integers returns its tagged result from the public entry in eleven steps when the divisor exceeds one. |
| `division-gcd-word-loop-correct` and `division-gcd-word-loop-zero-first` | The checked word loop computes the Euclidean recurrence within the initial positive divisor magnitude many iterations. A zero first magnitude takes one iteration. |
| `division-public-immediate-gcd-returns` and `division-public-gcd-by-one-returns` | The public immediate path returns the nonnegative tagged GCD with a positive second operand. It returns the second operand when the first is zero. When either operand is one, the unit path returns tagged one. |
| `division-boxed-setup-prepares-views-and-workspace` | The boxed prefix saves the mode, obtains operand counts, requests five work buffers, refreshes both views after reservation, and initializes the remainder slot. |
| `division-step-reaches-divide`, `division-boxed-call-enters-divider`, and `division-boxed-saves-quotient-sign` | The boxed call setup passes the magnitude views and three work addresses with the link intact. The quotient path saves the sign from the actual dividend view. |
| `division-gcd-copies-initialize-rotation` | Two checked copy calls initialize the GCD loop with physical integer views of both operands and the rotating work addresses. |
| `division-boxed-gcd-select-runs`, `division-boxed-gcd-euclidean-step`, and `division-boxed-gcd-finishes-with-natural-view` | The checked GCD loop selects its case, rotates the physical buffers after division with a strictly decreasing second magnitude, and prepares a nonnegative GCD view for second magnitude zero or one. |
| `division-boxed-gcd-iteration-executes` and `division-boxed-gcd-loop-computes-natural-view` | The checked division call, remainder rotation and base cases compose into a Euclidean loop. Its result is a normalized nonnegative view, and the number of continuing iterations is bounded by the original second magnitude. |
| `division-boxed-exact-quotient-writes-signed-view` and `division-boxed-restores-frame-and-reaches-pack` | The boxed exact-quotient suffix writes the sign to the quotient view. The shared epilogue restores the saved registers and SP and tail-calls packing. |
| `division-boxed-finishes-through-pack` and `division-boxed-exact-quotient-returns-from-views` | The shared epilogue returns a datum under the pack contract. The exact-quotient theorem connects the refreshed boxed operand views to that datum. |
| `division-public-boxed-exact-quotient-returns` and `division-public-boxed-gcd-returns` | Under successful setup and the stated call contracts, the public boxed entries return a datum for the signed exact quotient or for the nonnegative integer satisfying `proof-gcd-p`. The result uses the canonical immediate encoding when it fits. The GCD of a zero first operand and positive second operand returns the value of the second operand. |

The execution examples certify runs on bytes assembled from the
compiler runtime. They cover a one-limb divisor, a two-decrement
estimate, add-back, a nonzero normalization shift, a short dividend,
both quotient representations, and both GCD representations. Each
GCD path includes a zero-first-operand example.

`division-example-divider-path-premises` checks the premises of the
uniform divider theorem on short, one-limb and multi-limb inputs.
`division-example-normalizer-trims-two-zero-limbs` checks a normalization
call on the limbs `(17 0 0)`. It returns the normalized view of 17 in
22 instructions.

`division-raw-model-clz-coverage` is the single-instruction witness
for `(:clz 10 10)`: the model's `a64-decode` and the foundation
decoder both decode the assembled word `#xdac0114a` as that
instruction.

## Remaining obligations

General image placement requires establishing that later label updates
and fragment emission preserve the expected division slices for
arbitrary generated functions and data, then connecting the slices to
the loader's mapped executable spans. The placement theorem takes
fragment agreement as a premise.

The divider and boxed theorems take checked phase conditions for
instruction placement, mapped accesses, stack slots and disjoint
buffers. The long traversal assumes the physical layout and
access conditions along the execution. The checked normalization
callee supplies `division-unsigned-normalize-return-p` under its
instruction, memory and argument conditions. The divider suffix
uses this contract for the two calls. The boxed prefix assumes
`division-boxed-view-call-return-p` for each view call and the
foundation's `proof-integer-reserve-return-p` for successful
reservation. The boxed returns use `division-pack-call-contract-p`
for the result datum and return frame. The view, reservation and
packing call proofs, the collector and resource-stop paths, and the
derivation of all phase conditions from the top-level mapped image
and stack and heap invariants are separate proof obligations.

## Certification

Run the following commands from the repository root.

```sh
SBCL_USER_ARGS='--dynamic-space-size 2500' sh compiler/single/proofs/certify.sh --foundations
sh compiler/single/proofs/division/certify.sh
```

On 2026-11-26, ACL2 8.7 certified the foundations and all 70 books
in this directory. The first command printed
`Compiler proof foundations certified.` The second printed
`Certified compiler/single/proofs/division/examples.lisp.` as its last
certification line. The book logs are staged under
`build/compiler/single/proofs/`.
