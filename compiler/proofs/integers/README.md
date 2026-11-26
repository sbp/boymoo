# Integer representation, arithmetic and bits

These books carry work package P8 of `compiler/proofs/README.md`. They
are about the integers of compiled programs: how an integer is laid out
as a tagged word or as a boxed object of base 2^32 limbs, the
arithmetic on those limbs, the bit operations, and the integer
routines of `compiler/runtime.lisp`. They use the certified books in
`compiler/proofs/foundations/`, in particular `interfaces.lisp`, and the A64 model
in `compiler/model/`.

Every book is certified by ACL2 in logic mode with no axioms, no
skipped proofs and no trust tags. The books prove their arithmetic
from the definitions of `floor`, `mod`, `ash`, `logand`, `logior` and
`logxor`; they include no book outside this repository.

## Terms

- A *limb* is a natural number below 2^32. A boxed integer stores its
  magnitude as a list of limbs, least significant first, and its sign
  as a separate word, 0 for nonnegative and 1 for negative.
- A limb list is *normalized* when its last limb is not zero. Zero is
  the empty list.
- An *immediate* integer is one in the range from -2^62 to 2^62 - 1
  (`proof-immediate-integer-p` in `compiler/proofs/foundations/values.lisp`). Its
  *tagged word* is 2v + 1 modulo 2^64 (`proof-integer-word`).
- The *integer view* of a boxed integer is the predicate
  `proof-integer-view-p` of `compiler/proofs/foundations/interfaces.lisp`: a header
  word of type 3 whose size field counts the sign and limb words, a
  sign word, and normalized limbs whose signed value is the integer.

## What the books prove

### `words.lisp`: division by a positive number and machine words

- `integer-floor-bounds`, `integer-floor-scaled-bounds`,
  `integer-floor-unique`: the floor of x by y > 0 is the unique integer
  q with q·y ≤ x < (q + 1)·y.
- `integer-floor-and-mod-decomposition`, `integer-mod-unique`,
  `integer-mod-bounds`: x = mod(x, d) + d·floor(x, d) with
  0 ≤ mod(x, d) < d, and the remainder is the unique such number.
- `integer-logand-low-mask`: the bitwise AND of x with 2^w − 1 is
  x modulo 2^w.
- `integer-a64-unsigned-is-mod`: the model's `a64-unsigned` of width w
  is reduction modulo 2^w, so every register write of the model is
  reduction modulo 2^64.

### `limbs.lisp`: base 2^32 carry, borrow and multiply-accumulate

- `integer-limb-add-correct`: adding two limbs and a carry bit gives a
  limb and a carry bit whose value, digit + 2^32·carry, is the sum.
- `integer-limb-subtract-correct`: subtracting a limb and a borrow bit
  from a limb gives a limb and a borrow bit with
  digit − 2^32·borrow equal to the difference.
- `integer-limb-multiply-accumulate-word-bound` and
  `integer-limb-multiply-accumulate-correct`: for limbs a, b, old and
  carry, a·b + old + carry is below 2^64, so it fits one machine word,
  and it splits into a limb digit and a limb carry.
- `integer-add-limbs-correct`, `integer-subtract-limbs-correct`,
  `integer-subtract-ordered-limbs`: the carry and borrow chains over
  whole limb lists compute the sum and, when the subtrahend is not
  larger, the difference with no final borrow.
- `integer-multiply-row-correct`: one row of schoolbook multiplication,
  a limb factor times a limb list accumulated into an existing row,
  adds factor·value to the row and leaves the limbs above the row
  unchanged.

### `signed-words.lisp`: shifts, signed words and tagged words

- `integer-ash-left` and `integer-ash-right`: `ash` by a count of n is
  multiplication by 2^n, and by −n is the floor of division by 2^n.
- `integer-a64-signed-test`, `integer-a64-signed-in-range`: the model's
  `a64-signed` reads the top bit as the sign and is the identity on
  the signed range of its width.
- `integer-immediate-word-signed`, `integer-immediate-word-odd`,
  `integer-immediate-word-type`: the tagged word of an immediate v is
  a 64-bit word, odd, whose signed reading is 2v + 1.
- `integer-immediate-word-round-trip`: the tagged word of an immediate
  integer is a view of that integer under `proof-value-p`, whatever
  the heap.

### `representation.lisp`: limbs in memory, normalization, comparison and packing

- `integer-trim-limbs-correct` and `integer-trim-signed-value`:
  removing high zero limbs gives a normalized list with the same
  value, and setting the sign of zero to 0 keeps the signed value.
- `integer-compare-magnitudes-correct`: comparing normalized limb
  lists first by length and then limb by limb from the top gives the
  order of their values.
- `integer-compare-signed-correct`: the same with signs, for
  normalized sign and limb pairs.
- `integer-pack-immediate-test-correct`: a normalized signed limb list
  has at most two limbs and a magnitude below 2^62 + sign exactly when
  its value is immediate. This is the test that decides whether a
  result is packed into a tagged word.
- `integer-limb-value-of-read`, `integer-normalized-limbs-of-read`:
  the limbs read from memory have the value and normalization that
  `proof-limb-magnitude` and `proof-limbs-p` of the foundations give.
- `integer-header-fields`, `integer-header-count`: the header word
  3 + 2048·(1 + n) of a boxed integer with n limbs has type 3, a size
  of 8·(1 + n) bytes, and gives back 1 + n when shifted right by 11.
- `integer-memory-view` and `integer-memory-view-components`: a header,
  sign word and normalized limbs laid out at an address within one
  span form an integer view, and every integer view has that layout.
- `integer-binary-reservation`: the reservation of 8·(3 + l + r) bytes
  that a binary operation on integers with l and r limbs makes is a
  multiple of 8, is large enough for a sum, a difference or a product
  of the operands, and fails the allocation bound exactly when it
  exceeds the space size of the foundations.

### `bits.lisp`: two's complement bit operations

- `integer-logior-split`, `integer-logxor-split`, `integer-logxor-half`:
  each bit operation splits into its low bit and the operation on the
  halves.
- `integer-floor-of-logxor` and `integer-mod-of-logxor`: XOR commutes
  with shifting right by w bits and with taking the low w bits. The
  second is what lets the runtime compute an XOR one 32-bit
  two's-complement digit at a time.
- `integer-logxor-of-doubled-integers`: the XOR of two tagged words
  with the same tag bit is twice the XOR of the integers, which is the
  immediate path of the LOGXOR entry before it adds the tag back.
- `integer-negative-right-shift-rounds-down`: shifting −m right by s
  bits gives −(floor(m / 2^s) + 1) when any discarded bit of m is set
  and −floor(m / 2^s) otherwise. This is the rule by which
  `rt:z-shift` rounds the magnitude of a negative integer up.
- `integer-right-shift-to-sign`: a shift right by s of a number whose
  magnitude is below 2^s gives its sign, 0 or −1.

### `ash-immediate.lisp`: the right-shift branch of the ASH entry

- `integer-ash-immediate-right-shift`: let v be an immediate integer
  and k a positive count. Shift the tagged word of v right
  arithmetically, by the model's `a64-shift` of kind 2, by k limited
  to 63. Then clear its low bit and add one modulo 2^64. The result is
  the tagged word of `(ash v (- k))`, and that integer is immediate.
  This is the arithmetic of the label `rt:ash-right` in the entry
  `jet:COMMON-LISP::ASH`, with the two bitfield instructions that
  clear the low bit written as twice the floor of half.

### `runtime-image.lisp`: the runtime image

- `runtime-image.lisp` assembles the Linux system code and the runtime
  code of `compiler/runtime.lisp` with `a64-layout` and `a64-bytes`,
  and decodes it, so that other books can refer to the address and the
  decoded instructions of each runtime label
  (`integer-runtime-address`, `integer-runtime-instructions`).

### `ash-right-branch.lisp`: the right-shift branch, instruction by instruction

The function `integer-run-straight` executes a list of decoded
instructions one after another with the model's `a64-execute`. The
instructions are those that `integer-runtime-instructions` decodes from
the assembled runtime image, so the theorems are about the bytes the
compiler emits, not a copy of them.

- `integer-ash-right-limit-instructions`: the first four instructions
  after `rt:ash-right` (negate, move 63, compare, select if lower or
  same) leave in x2 the count limited to 63, and leave x0 unchanged,
  when x2 held the 64-bit pattern of a count from −2^62 to −1. The
  condition flags are computed by the model, not assumed.
- `integer-ash-right-shift-instructions`: the last four (arithmetic
  shift right by x2, logical shift right by one, logical shift left by
  one, add one) leave in x0 the value that
  `integer-ash-immediate-right-shift` describes, for any x2 below 64.
  `integer-logical-shift-right-one` and
  `integer-logical-shift-left-one` give the effect of the two bitfield
  instructions through the model's rotation `a64-ror`.
- `integer-ash-right-branch-correct`: on any machine whose x0 holds
  the tagged word of an immediate integer v and whose x2 holds the
  64-bit pattern r of a count from −2^62 to −1, the eight instructions
  after `rt:ash-right` leave in x0 the tagged word of
  `(ash v (- r 2^64))`. That is the value that `core-prelude` gives
  for `ASH` of v and that count, since it applies `core-ash`, which
  `core-ash-is-ash` in `compiler/model/core.lisp` proves equal to
  `ash`; for `BINARY-LOGXOR` it applies `binary-logxor` itself. The
  entry reaches this label when both
  arguments are tagged immediate integers, the first is not zero and
  the count is negative; the entry has then put the count in x2 by an
  arithmetic shift right of x1 by one. When the first argument is
  tagged zero the entry returns it at once.

### `logxor-immediate.lisp`: the immediate path of the LOGXOR entry

- `integer-logxor-of-immediates-is-immediate`: the XOR of two
  immediate integers is immediate.
- `integer-logxor-immediate-words`: the XOR of the tagged words of two
  immediate integers, plus one modulo 2^64, is the tagged word of
  their XOR.
- `integer-logxor-immediate-path-correct`: on any machine whose x0 and
  x1 hold the tagged words of immediate integers a and b, the two
  instructions at byte offset 12 of `jet:ACL2::BINARY-LOGXOR` (XOR of
  x0 with x1, then add one) leave in x0 the tagged word of
  `(logxor a b)`. The entry reaches them exactly when both arguments
  are tagged immediate integers.

### `ash-left-branch.lisp`: the left-shift branch of the ASH entry

For a nonnegative count c of at most 62 on immediate operands, the ASH
entry subtracts one from the tagged word of v, giving the 64-bit
pattern X of 2v, shifts X left by c into Y, shifts Y back right
arithmetically by c, and compares the outcome with X. When they are
equal it returns Y plus one; otherwise it calls `rt:n-ash`.

- `integer-left-shift-test-sound`: if shifting Y back gives X, then
  the signed reading of Y is exactly 2v·2^c, so v·2^c is immediate and
  Y plus one modulo 2^64 is its tagged word. `integer-signed-window-equal`
  (two integers of the signed 64-bit range that agree modulo 2^64 are
  equal) carries the argument.
- `integer-ash-immediate-left-shift`: the same statement with the
  model's shifts `a64-shift` of kinds 0 and 2.
- `integer-ash-left-shift-steps` and `integer-ash-left-return-step`:
  the three instructions at byte offset 40 of `jet:COMMON-LISP::ASH`
  put X, Y and the shifted-back value in x3, x4 and x5, and the
  instruction at byte offset 60 puts x4 plus one in x0.
- `integer-ash-left-branch-correct`: on any machine whose x0 holds the
  tagged word of an immediate integer v and whose x2 holds a count c
  from 0 to 62, if after the three instructions x5 equals x3, then the
  instruction at byte offset 60 leaves in x0 the tagged word of
  `(ash v c)`, and that integer is immediate. The entry reaches byte
  offset 40 for such operands, and goes on to byte offset 60 after
  comparing x5 with x3 and finding them equal.
- `integer-ash-left-compare-step`: the comparison at byte offset 52
  sets the flags, as the model computes them, so that the condition
  "not equal" of the branch at byte offset 56 holds exactly when x5
  differs from x3. The branch therefore falls through to byte offset
  60 exactly when x5 equals x3, which is the hypothesis of
  `integer-ash-left-branch-correct`.

### `ash-count.lisp`: the count and the choice of branch in the ASH entry

- `integer-ash-count-step`: when x1 holds the tagged word of an
  immediate count c, the instruction at byte offset 20 of
  `jet:COMMON-LISP::ASH`, an arithmetic shift right by one, leaves the
  64-bit pattern of c in x2. This is the form of x2 that
  `integer-ash-right-branch-correct` (for c from −2^62 to −1) and
  `integer-ash-left-branch-correct` (for c from 0 to 62) assume.
- `integer-ash-count-sign-test`: with that pattern in x2, the
  comparison at byte offset 24 makes the condition "less than" of the
  branch at byte offset 28, which goes to `rt:ash-right`, hold exactly
  when c is negative.
- `integer-ash-count-size-test`: for c from 0 to 2^62 − 1, the
  comparison at byte offset 32 makes the condition "greater than" of
  the branch at byte offset 36, which goes to `rt:n-ash`, hold exactly
  when c exceeds 62.

### `entry-tests.lisp`: the first tests of the ASH and LOGXOR entries

- `integer-immediate-pair-test`: the AND of x0 and x1 and the test of
  its low bit, at byte offset 0 of `jet:ACL2::BINARY-LOGXOR` and byte
  offset 8 of `jet:COMMON-LISP::ASH`, make the condition "equal" of
  the branch that follows, which leaves the immediate path, hold
  exactly when x0 or x1 is even.
- `integer-immediate-pair-test-of-words`: when x0 and x1 hold the
  tagged words of immediate integers, that condition is false, so both
  entries stay on their immediate paths.
- `integer-ash-zero-test` and `integer-tagged-word-is-one`: the
  comparison at byte offset 0 of the ASH entry makes the condition
  "equal" of the branch at byte offset 4, which returns x0 at once,
  hold exactly when x0 is 1, and the tagged word of an immediate
  integer is 1 exactly when the integer is zero. Since `(ash 0 c)` is
  0, returning x0 there is correct.

### `logxor-path.lisp`: the whole immediate path of the LOGXOR entry

- `integer-logxor-path-steps`: when x0 and x1 are odd, the first five
  instructions of `jet:ACL2::BINARY-LOGXOR` (AND, test of the low bit,
  branch if equal, XOR, add one), executed one after another, leave in
  x0 the XOR of x0 and x1 plus one, each reduced modulo 2^64, and
  leave the program counter 20 bytes on, so the branch falls through.
- `integer-logxor-immediate-whole-path`: on any machine whose x0 and
  x1 hold the tagged words of immediate integers a and b, those five
  instructions leave in x0 the tagged word of `(logxor a b)` and the
  program counter at the return instruction 20 bytes after the entry.

### `runtime-examples.lisp`: the runtime on the model

- `runtime-examples.lisp` loads the runtime image into a model machine with a
  stack, a value stack and a heap, places integer arguments as tagged
  words or boxed objects, and runs it with `proof-run` until it returns.
  Its assertions check, on chosen arguments, that `rt:z-add-op`,
  `rt:z-negate-op`, `rt:z-multiply-op`, `rt:z-compare` and the entries
  for `ASH` and `BINARY-LOGXOR` return the value that `core-prelude`
  gives, with the stack pointer and value stack restored. The cases
  cover immediate and boxed operands of both signs, carries across the
  immediate boundary, noninteger operands, negative right shifts with
  and without discarded bits, and boxed shift counts. One assertion
  checks that a left shift by 2^62 reaches the resource stop: exit 3
  with the message `memory exhausted: a number is too large` on
  descriptor 2.

## Why `rt:z-shift` asks for a nonzero integer

The comment before `rt:z-shift` in `compiler/runtime.lisp` asks for "a
nonzero integer datum in x0". `zero-shift.lisp` shows why on the model:
when x0 is zero and the shift is positive, the view of zero has no limbs,
and the left-shift loop tests its limb counter only after the first limb,
so it runs on until a load faults. The first assertion of the book shows
this with x0 tagged zero and x1 equal to 1.

No compiled program appears to call `rt:z-shift` with zero. The only
branch to `rt:z-shift` is in `rt:n-ash`, whose only callers are the
branches of the entry `jet:COMMON-LISP::ASH`. That entry
returns at once when x0 is tagged zero (`integer-ash-zero-test` and
`integer-tagged-word-is-one` above); `rt:n-ash` returns zero itself
when x0 is not an integer; and `rt:z-pack` gives every integer whose
magnitude is below 2^62 the immediate form, so a boxed integer made by
the runtime is never zero. Apart from the test of the entry, which is
proved here, these facts come from reading `compiler/runtime.lisp` and
are not proved. On 2026-11-26 the command
`grep -n '"rt:z-shift"\|"rt:n-ash"' compiler/runtime.lisp` listed,
besides the two labels, the one branch to `rt:z-shift`, inside
`rt:n-ash`, and the three
branches to `rt:n-ash`, all inside the ASH entry. The second
assertion of the book shows that the entry gives 0 for `(ash 0 1)`,
`(ash 0 62)` and `(ash 0 (expt 2 62))`.

## What is not proved yet

These are open goals of P8.

- The machine-level contracts of the helpers in `runtime-integer-code`
  for all inputs: `rt:z-reserve`, `rt:z-view`, normalization, packing,
  comparison, signed addition and multiplication, with their scratch
  and result conditions. The books prove the arithmetic that each
  helper relies on, but not that the instructions compute it.
- `runtime-bit-code` (`rt:n-ash`, `rt:z-xor` and `rt:z-shift`) for all
  inputs, including two's-complement digits on the machine and the
  boxed-count branches.
- The paths of the ASH and LOGXOR entries that call `rt:n-ash` and
  `rt:z-xor-op`.
- One theorem for each whole immediate path of the ASH entry. The
  theorems of `ash-right-branch.lisp`, `ash-left-branch.lisp`,
  `ash-count.lisp` and `entry-tests.lisp` cover the straight-line
  pieces, executed with `a64-execute`, and the flags that decide each
  branch between them, but do not yet join the pieces through the
  branch instructions' effect on the program counter.
  `logxor-path.lisp` does this for the LOGXOR entry.
- Execution from memory. Every theorem about instructions here runs a
  list of instructions decoded from the assembled runtime image with
  `integer-run-straight`. None yet runs the fetch and step loop
  `proof-run` of the foundations on a loaded image, or follows the
  return through x30, as the contracts of
  `compiler/proofs/foundations/interfaces.lisp` require.
- Integer-result and resource-bound theorems for the `rt:z-*-op`
  entries used by fraction and complex code.

The assertions of `runtime-examples.lisp` check these routines only on
the arguments they name.

## Certifying

Certify the foundations once, then these books, from the repository
root:

    sh compiler/proofs/certify.sh --foundations
    sh compiler/proofs/integers/certify.sh

The second command certifies, in order, `words`, `limbs`,
`signed-words`, `representation`, `bits`, `ash-immediate`,
`runtime-image`, `ash-right-branch`, `logxor-immediate`,
`ash-left-branch`, `ash-count`, `entry-tests`, `logxor-path`,
`runtime-examples` and `zero-shift`.

On 2026-11-26, with ACL2 8.7 and the foundations already certified,
`sh compiler/proofs/integers/certify.sh` printed one line
`Certified compiler/proofs/integers/BOOK.lisp.` for each of the
fifteen books above, in that order, and exited with status 0, in 33
seconds of elapsed time. The facts stated in this file, including the
assertions about runtime runs and the reason for the contract of
`rt:z-shift`, are the theorems and assertions of these books, so that
command checks them all.
