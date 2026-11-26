# Proof of the compiler

The subject is `BOYMOO-COMPILER::COMPILE-TEXT` and the instruction
semantics of `compiler/model/`. See the interfaces and file formats in
`compiler/README.md`, the source semantics in `compiler/model/core.lisp`,
and the program text in `spec/formats.md`.

## The theorem

Take a well-formed program text in the compiler's input format with
target Linux. The theorem is stated for a text without a `heap-limit`
line: the foundations fix each of the collector's spaces at its default
size, `*proof-space-size*`, and the static-block theorems of P3 exclude
the word that such a line adds. Supply the ground and library lines
that it uses.
Interpret its names in an ACL2 world with its package declarations and
imports. Take the effective definitions and attachments in the order
specified by the format, with well-scoped terms, consistent arities
and acyclic attachment chains. Let `entry` name a one-argument
invocation and let `input` be a string of bytes. An entry with an
effective definition or routine has arity one. A name with neither a
definition nor an attachment can be the entry for a no-value case.
Compare the following computations.

1. Evaluate `(core-call entry (list input) program fuel)` in the source
   model.
2. Apply `compile-text` to the program text, load the resulting ELF
   bytes, and run the A64 machine from the ELF entry. Supply `input` to
   descriptor 0 and apply the Linux system-call rules in the foundations
   at each SVC. The shared entry points are `proof-source-result` and
   `proof-compiled-start`.

When the source result is a string, execution with successful input
and output calls and sufficient resources reaches exit 0 with that
string, byte for byte, on descriptor 1. A source no-value result, or a
source value other than a string, reaches exit 1 with empty descriptor 1
output. Execution may instead reach exit 3 with empty descriptor 1
output if it reaches a resource limit. The proof of that alternative
identifies the failed bound or failed mapping request and proves that
the corresponding check leads to the stop. Input and output errors have
a separate status 2 obligation for prefixes admitted by the kernel
rules. Output can be partial on a write error.

The theorem states the progress implication for every finite source
evaluation whose result is other than `:out-of-fuel`: a finite machine
step count, with bounds on the required stack, heap, mappings and
kernel replies, or a proof of the resource stop. It states the converse
for every modeled exit 0 or 1, which gives a sufficient source fuel and
the corresponding result. Source fuel bounds evaluation depth and machine
fuel bounds executed instructions. An exhausted proof counter supplies
neither a source result nor a resource stop. A machine fault, an
undefined instruction, or a missing kernel reply supplies neither.
For source evaluations of unbounded depth the converse remains
meaningful. A finite-exit guarantee requires a source termination
argument or a reachable resource check. A further theorem states that
the text is accepted and that its assembled fields fit under the stated
compilation bounds. Those bounds are separate from exhaustion in the executable.

The loader theorem covers the ELF files of this compiler under the
single-load-segment interpretation in the System V and AArch64 ELF
ABIs. The kernel contract describes isolated execution with ordinary
private mappings and byte streams. Mach-O needs a separate loader,
entry and syscall proof, including a statement of what dyld assumes
about signatures and the initial machine. The source, generator, data
and instruction obligations apply to that target as well.

## Shared books and proof boundaries

The following names are relative to `compiler/proofs/foundations/`.

| Book | Interface |
|---|---|
| `machine` | The model's instruction step. Its decoder repeats the model's decoding of CLZ and of the conditional compare used in an assembler expansion. It also gives byte spans and the code placement relation. |
| `kernel` | A machine with mapped regions, byte streams and a sequence of kernel replies. It gives checked steps, finite execution to a cutpoint, and the Linux SVC rules. |
| `loading` | Recognition of the ELF subset and loading into the same machine and mapping representation. |
| `values` | The published object map, interpretation of tagged words, and value and internal vector views. |
| `heap` | Runtime metadata, shape of heap spaces and stacks, published objects, stable bytes, static tables, and roots. |
| `interfaces` | The common include, source results, frame and routine boundary predicates, allocation and stop interfaces, and finite execution observations. |

Books use the `BOYMOO-PROOFS` package. A package includes
`../foundations/interfaces` in its first book. It may use the other
foundation books directly for smaller sublemmas. The common include
brings in the actual compiler and the source and machine models. The
foundations are shared as fixed definitions. A package records a needed
extension or correction with its affected statements.

A *cutpoint* is an address at which an execution segment stops before
executing the instruction at that address. Concrete segments are
stated with `proof-run` and `proof-segment-p`. For a routine call, a
proof shows that the machine reaches the callee label with its inputs
and link installed and the callee's precondition met. The continuation
quantifies over the state supplied at the return address and assumes
the named callee's postcondition on those two states. A nonreturning continuation uses the
callee's stop obligation. The results compose by instantiating each
hypothesis with the segment and witnesses from the callee's proof and
adding the step counts. Internal loops, direct and tail calls, and
traps follow the same cutpoint convention. This permits each package to
certify while every other package directory is empty. A hypothesis
about a run is an explicit premise of a theorem. A final theorem
requires a proof that discharges it. The checked model advances with
`proof-advance` and adds segment lengths with `proof-advance-append`.
A proof with named cutpoints also shows that the segments do not reach
their final cutpoint early.
P1 establishes `proof-instruction-at-p` or
`proof-instructions-at-p` for the emitted bytes. A routine or
generator theorem can take those placement facts as premises and
use `proof-step-from-instruction` with the checked memory premises.

The object map supplied to `proof-view` and `proof-heap-p` is a
mathematical witness. It records published addresses, kinds, and
ranks, which decrease along references. It may omit unreachable
storage and reserved scratch. A call that collects can supply a new
map and different words for old roots. The view of each retained root
is the same. Temporary reservations have a separate span condition
until their fields are initialized. At an allocation or collection
cutpoint, every live movable datum is in the initialized part of the
value stack or in the dynamic symbol-table root. A routine may use
additional unpublished scratch on a segment that cannot collect.
Machine registers are compared by bits, and live datum slots by their
views. A postcondition exposes changed static-symbol roots and kernel
mappings.

The bounded static block occupies fewer than 2^32 bytes. This gives
one common bound on the lengths of static strings and list spines in
sequence proofs. The active space has its own four-gibibyte bound, and
separately mapped string lengths are below 2^32. A resource
case proves a violated inequality in `proof-resource-bound-p` or a
failed mapping request in `proof-mapping-refused-p` at the relevant
step, and then the path to the stop label in `proof-resource-label`
and the exit observation.

### The kernel boundary

`proof-load-linux` accepts a single read-execute load segment at the
ELF file base, with a writable initial stack supplied by the caller.
The mapped bytes include the file headers and the zero tail of the
last mapped page. A checked step requires a mapped instruction and
permissions for its memory accesses. A syscall consumes one supplied
reply except when it exits. A successful `mmap` reply selects a fresh
page-aligned interval of the requested rounded size. Valid
`madvise` and `munmap` requests succeed, clearing or removing the
requested writable interval. Reads consume a prefix of descriptor 0
and return zero at end of input for a positive request. Writes append
the reported prefix to descriptor 1 or 2. A negative Linux error
reply to a read or write leaves the stream unchanged. A zero-byte
write on a positive request is an I/O stop in the runtime. Returning
SVCs resume one instruction later, replacing X0 and preserving the
other registers and flags. The progress statement ranges over reply
policies that supply an admissible reply whenever a returning syscall
is reached. The model consumes the finite prefix used by the
terminating execution. A finite supplied list can witness that prefix.

### Linking the contracts

Public primitives and prelude functions use `proof-runtime-pre-p` and
`proof-runtime-return-p`. The input argument list consists of
source values represented in X0 onward. A returned state represents
the result of `core-primitive` or `core-prelude`, restores the
specified registers and stack prefix, and preserves existing symbol
identities. `proof-datum-return-p` gives the same form for private
helpers whose result is stated as a mathematical value.
`proof-compiled-entry-p` and `proof-compiled-return-p` use stack
arguments for a generated call, and `proof-environment-p` connects
its slots to source bindings. The stop cases use the source or
resource observation test in `interfaces` and a segment reaching
that exit.

A growth call uses `proof-grow-return-p`. An allocation call
returns `proof-allocator-return-p`, with
`proof-fast-allocation-return-p` when `proof-allocation-fits-p`
holds. The collection continuation assumes
`proof-collector-return-p`. Private number calls use
`proof-integer-view-p`, `proof-integer-reserve-return-p`,
`proof-exact-quotient-p` and `proof-gcd-p` where they apply.
String constructors return `proof-string-constructor-return-p`.
The premises of a theorem name the precondition, the stop alternatives
and the returning postcondition of each boundary that it imports.

A source term and its compiler term agree when a variable or call
head spells the canonical source symbol, a quoted compiler constant
spells the source datum, and the relation holds component by component
for `if`, applications, lambdas and the three fields of an `mbe`.
For compiler context, each arity lookup gives the arity of the
effective definition, and each attachment lookup gives the terminal
name of the source chain. `proof-index-agrees-p` states those lookups,
and `proof-constant-map-p` the canonical texts and quoted source data. A constant entry gives a tagged word or an
immediate integer to be tagged by the generator. The generator
assumes these facts only for the scope and lookups it uses. The
text and data proof establishes them from the format. The handling of
bad or unrepresentable input is a separate proposition, in which
reasoning about compiler errors in ACL2 distinguishes the compiler's
execution from the logical value of `hard-error`.

## Certification

Run `sh compiler/proofs/certify.sh` from the repository root.
The script stages and certifies the compiler and model source books
under `build/compiler/proofs/`, certifies the foundations there, and
then invokes each package directory's `certify.sh`. Use
`sh compiler/proofs/certify.sh --foundations` to prepare the shared
books for a single package run. Staging matches the certificates to
the copies of the sources in the checkout where the script runs.

On 2026-11-26, ACL2 8.7 certified 743 books with the commands that
`sh compiler/proofs/certify.sh` runs one after another:
`sh compiler/proofs/certify.sh --foundations` certified the 14 staged
compiler and model books and the 7 foundation books in 27 seconds, and
the `certify.sh` of each of the twelve packages below, run six at a
time, certified its books and exited with status 0, the longest,
`sequences`, in 742 seconds:

| Package | Directory | Books |
|---|---|---:|
| P1 | `assembly` | 71 |
| P2 | `generated` | 103 |
| P3 | `data` | 91 |
| P4 | `linux` | 6 |
| P5 | `allocation` | 61 |
| P6 | `primitives` | 34 |
| P7 | `collection` | 76 |
| P8 | `integers` | 15 |
| P9 | `division` | 70 |
| P10 | `numbers` | 74 |
| P11 | `sequences` | 92 |
| P12 | `symbols` | 29 |

The `README.md` of each package directory says what its books prove
and what they leave open. The foundations' `checks` book exercises CLZ
and the two-instruction zero-source expansion, including their flag
and register effects. It checks representative data views, the heap
invariant on a block from `data-build`, and an assembled ELF example
with mapping, reading, short writes and exit. The command's ACL2 logs
are in `build/compiler/proofs/`.

## Work packages

The proof is divided into the twelve packages below. Each has its own
directory, which holds its books, a `certify.sh` and a `README.md`
that says what the books prove and what they leave open. Each
package's `certify.sh` runs from the repository root after
`sh compiler/proofs/certify.sh --foundations`, and invokes
`sh compiler/proofs/certify.sh --books NAME BOOK ...` with the book
basenames in dependency order. The dispatcher finds the package
scripts by their directories. ACL2's output is written under
`build/`, and every book is certified in logic mode with skipped
proofs, added axioms and trust tags disallowed. Where an obligation
fails, a package gives a smallest checked counterexample, or a
statement for the range that certifies, and names the open
obligation.

Each section below gives a package's goal, the foundation books it
builds on, what it assumes of the other packages, and when it is
complete.

### P1. Instruction semantics and assembly

The books are in `compiler/proofs/assembly/`. They build on
`machine`, `kernel` and the compiler's `a64` book through `interfaces`.

The goal is that `a64-layout` assigns each label the sum of the
`a64-image-item-size` values before it, with unique labels, and that
the actual label table gives those offsets; that the fragments from
`a64-assemble-image` flatten to the exact concatenation of item bytes
and that the returned offset is the requested entry; and that, for
every executable item, fetching at the image base plus its offset
decodes to its specified instruction and executes the item's
register, flag, memory and PC effect. The field, alignment and
register-overlap premises are stated independently of `a64-word`.
The statements cover the multiword `:adr-far` and flag-setting
zero-source expansions, `:and-mask` with destination 31, `:cset :al`,
SP versus the zero register, signed branch displacements, and all
data items and padding. `:adr-far` uses a 4,096-byte aligned image
base. Reusable rules cover straight-line runs, conditional branches,
BL, BLR and RET with the convention used by `proof-run`.

The package is complete when every item has its decoding rule and a
linked-image execution lemma holds. A certified layout and a table of
proved per-item decoding rules are useful on their own.
`sh compiler/proofs/assembly/certify.sh` certifies it.

### P2. Generated terms and calls

The books are in `compiler/proofs/generated/`. They build on
`machine`, `heap` and `interfaces`, and assume linked bytes and
context agreement, the routine boundaries in `interfaces`, and the
prologue stop and grow contracts.

The goal is a joint induction for `gen-term`, `gen-args` and
`gen-lambda-args` against `core-eval-step` for terms, argument lists
and named calls. In a non-tail context, the next PC is the fragment's
continuation, X0 represents the source value and the occupied stack
prefix has its input views. The high-water bound holds on every
temporary push. The induction covers variable slots, quoted
constants, one branch of `if`, ordinary and resolved calls,
left-to-right argument evaluation, lambda variable aliases and lambda
scope, and selection of the logical `mbe` body. For `gen-routine`, it
covers the inline tag tests, loads and signed-overflow fast paths and
the slow call edge; for `gen-defined-call`, `gen-prologue` and
`gen-functions`, entry arity, argument transfer, the return link and
machine-frame restoration. In tail position the jump enters the
target with the caller's return link and its arguments compacted to
the current frame base, including when the new arity is larger, and
the callee's own return is the tail expression's return. The
named-call induction is on source fuel.

The package is complete when it covers the generated entry and all
term forms, with only the stated lower-layer hypotheses. A certified
prologue and tail transfer, or the non-call term cases and the stack
depth invariant, are useful on their own.
`sh compiler/proofs/generated/certify.sh` certifies it.

### P3. Static data and text agreement

The books are in `compiler/proofs/data/`. They build on `values`,
`heap` and `interfaces`, and assume a placement of the emitted
fragments at the selected heap base.

The goal is that `data-build` supplies the size and bytes of a static
block satisfying `proof-static-p`, with an initially empty dynamic
root, together with the static object map, in which every canonical
constant represents the parsed ACL2 datum. The package rows are
numbered in first-declaration order, visible if any declaration is
visible, and contain the exact imports and witness fields. The static
buckets give the home and imported name bindings using the hash of
`data-bucket-add`, and stored symbols are unique by home package and
name. The statements include NIL at word 34, T at word 58, dotted
lists, escapes and normalized numbers. A bridge relates
`read-program`, `index-lines` and `resolve-attachments` to the source
terms, latest bindings, arities and terminal targets, including the
extra entry definition and its synthetic argument, by binding and
slot, when `compile-entry-definitions` inserts a wrapper.

The package is complete when it connects canonical text to the image,
symbol and constant lookups used by P2 and the whole theorem. A
certified serialized constant lemma, package-row theorem or index
theorem is useful on its own. `sh compiler/proofs/data/certify.sh`
certifies it.

### P4. Linux loading, process entry and composition

The books are in `compiler/proofs/linux/`. They build on `machine`,
`kernel`, `loading`, `heap` and `interfaces`, and take the
linked-image, static-image, entry function and runtime obligations as
hypotheses.

The goal is that `elf-image-executable` gives a file accepted by
`proof-elf-p` for a sized image and an in-range aligned entry, that
`proof-load-linux` installs its exact fragments with executable
permission, and that the PC is the assembled `os:main`; that each
wrapper in `linux-system-code` reaches the expected Linux SVC with
the specified arguments and implements the wrapper result under the
kernel rules; that `rt:start` makes the initial mappings, copies the
static block, reads its input in a loop with EOF and the maximum-size
check, and calls `rt:entry` with its input slot; that `rt:write-all`
handles short writes; and that the exit and diagnostic paths of
`runtime-stop-code` give the descriptor, status, prefix, escaped
datum spelling and newline for successful diagnostic writes, and the
exit status when a diagnostic write fails. The diagnostic use of
`rt:package-row` assumes its contract. The whole theorem is stated by
expanding `compile-text` and composing these results with the
contracts of the other phases.

The package is complete when it gives the conditional whole theorem
with each lower obligation named and exposed. A certified ELF byte or
loader theorem, system call wrapper lemma, or input and output loop
invariant is useful on its own. `sh compiler/proofs/linux/certify.sh`
certifies it.

### P5. Allocation, stack growth and publication

The books are in `compiler/proofs/allocation/`. They build on
`machine`, `kernel`, `heap` and `interfaces`, and assume the collector
boundary for slow allocation and the system call and stop contracts.

The goal is that `rt:grow` and `rt:ensure-stack` agree with
`proof-grow-limit` within the value-stack reservation and reach the
stack-size stop outside it, with their separate clobber sets; that
`rt:alloc` and `rt:alloc-cells` reserve the precise unpublished span
and adjust the proper frontier and the shared budget, including
arithmetic overflow and the slow paths' request and mode; that for
`CONS` the stored fields represent both operands, including after
both value-stack roots are reloaded following a collection; that
`rt:new-large-string` rounds, tests the budget, maps zeroed memory,
inserts the mapping in its list, and gives the header and payload
address, or fails on an unrepresentable or refused request; and that
initializing a returned span admits its new objects to the published
map. The small string wrapper belongs to P11.

The package is complete when it supplies each growth and allocation
postcondition that callers use, including a symbolic slow-path
continuation. The fast paths and the publication lemmas are useful on
their own. `sh compiler/proofs/allocation/certify.sh` certifies it.

### P6. Tests, projections and equality

The books are in `compiler/proofs/primitives/`. They build on
`machine`, `values`, `heap` and `interfaces`, and assume stack growth
for `EQUAL`.

The goal is the runtime contract for `BAD-ATOM<=`, `CAR`, `CDR`,
`CONSP`, `CHARACTERP`, `STRINGP`, `SYMBOLP`, `INTEGERP`, `RATIONALP`,
`COMPLEX-RATIONALP`, `ACL2-NUMBERP`, `CHAR-CODE`, `CODE-CHAR`,
`NUMERATOR`, `DENOMINATOR`, `REALPART`, `IMAGPART` and `EQUAL`, with
the model's logical completions on every represented datum. For
equality, the value stack of deferred pairs represents the remaining
conjunction, byte comparison uses the declared length, and falling
through the symbol fast path relies on symbol identity. The contracts
give precise clobbers, preserve the incoming roots and allocate
nothing. They include the private tag, type, boolean and byte
comparison entries that these routines use.

The package is complete when it covers the named entries and all
cases of equality. The tag and projection lemmas and byte-span
equality are useful on their own.
`sh compiler/proofs/primitives/certify.sh` certifies it.

### P7. Copying collection

The books are in `compiler/proofs/collection/`. They build on
`machine`, `kernel`, `values`, `heap` and `interfaces`, and assume the
kernel wrapper contracts and `proof-fast-allocation-return-p` for the
final reservation of the pending span.

The goal is that `rt:forward` establishes or reuses a unique
forwarding entry, preserves static addresses, and marks an external
string without moving it; that, with deferred fields and the two
destination scan cursors modelled, every reachable object is copied
once, every field and root is fixed up, and sharing and views are
preserved; that the scan progresses by a measure over the original
graph and the work remaining, including discovery by either scan
cursor; that the four-gibibyte capacity test, the new budget and the
frontier arithmetic hold, only the retired pages are released, and
`rt:sweep-strings` respects reachability and resets the marks; and
that `rt:collect` restores its frame and gives its result span for
each request mode.

The package is complete when it gives the collection contract on the
full published graph, including mixed regions and the pending
allocation. A forwarding theorem, or one inductive scan-loop
invariant with explicit remaining obligations, is useful on its own.
`sh compiler/proofs/collection/certify.sh` certifies it.

### P8. Integer representation, arithmetic and bits

The books are in `compiler/proofs/integers/`. They build on `machine`,
`values`, `heap` and `interfaces`, and assume stack growth and
allocation.

The goal is each `runtime-integer-code` helper's view, scratch and
result contract, from `rt:z-reserve`, `rt:z-view`, normalization,
packing and comparisons through signed addition and multiplication,
with the base-2^32 carry, borrow and multiply-accumulate invariants;
`runtime-bit-code` and the `ASH` and `BINARY-LOGXOR` entry wrappers
against `core-prelude`, including two's-complement digits, the
discarded bits of a negative right shift and the boxed-count
branches; and integer-result and resource-bound theorems for the
`rt:z-*-op` entries that fraction and complex code use.

The package is complete when it covers the signed, boxed and
immediate paths, so that callers can assume an actual normalized
result or a justified stop. The common integer view and one certified
arithmetic kernel or bit operation are useful on their own.
`sh compiler/proofs/integers/certify.sh` certifies it.

### P9. Division and greatest common divisor

The books are in `compiler/proofs/division/`. They build on `machine`,
`values`, `heap` and `interfaces`, and assume the integer view,
packing, reservation and normalization contracts stated in the entry
comments.

The goal is that `rt:z-divide` produces normalized magnitudes `q` and
`r` with `a = b*q + r` and `0 <= r < b` for a nonzero divisor
magnitude `b`, by the one-limb loop and by the multi-limb loop, with
normalization related to CLZ, the quotient estimate bounded, and the
correction and the borrow and add-back steps proved, including carry
bounds and scratch ranges; and that the immediate and boxed wrappers
are correct for `rt:z-quotient` under its exact-division
precondition, and for `rt:z-gcd`, by Euclid's decreasing remainder,
with a nonnegative result, including a zero first operand with a
positive second operand.

The package is complete when it supplies both integer operations to
rational normalization. A certified one-limb result, a bound on the
quotient estimate, or one normalized long-division iteration is
useful on its own. `sh compiler/proofs/division/certify.sh` certifies
it.

### P10. Fraction and complex arithmetic

The books are in `compiler/proofs/numbers/`. They build on `machine`,
`values`, `heap` and `interfaces`, and assume integer arithmetic,
exact quotient, GCD, allocation and stack growth.

The goal is that `rt:q-normalize` and `rt:q-box` give the canonical
reduced rational, with a positive denominator and boxing exactly
where required; that `rt:c-box` gives a rational for a zero imaginary
part and a canonical complex object otherwise; that each generated
formula in `runtime-rational-code` computes its mathematical
operation and preserves every temporary value across allocation;
that the dispatch and completions of `BINARY-+`, `BINARY-*`,
`UNARY--`, `UNARY-/`, `<` and `COMPLEX` are correct, including the
reciprocal of zero, nonnumbers, nonrational components and the
lexicographic order of complex numbers; and that each helper taking
raw numerator and denominator fields has the precise divisibility
and representation premises it requires.

The package is complete when it gives the six public primitive
contracts. A certified formula-frame invariant or a complete rational
fragment is useful on its own. `sh compiler/proofs/numbers/certify.sh`
certifies it.

### P11. Sequences and coercion

The books are in `compiler/proofs/sequences/`. They build on
`machine`, `values`, `heap` and `interfaces`, and assume allocation
and stack growth, the string constructor contract for
`rt:new-large-string`, and the `UNARY--` and `BINARY-+` contracts used
to compute the size of a subsequence.

The goal is the small path of `rt:new-string` and `rt:empty-string`,
with an initialized header, padding, length and a returned writable
payload; `rt:string-view`, `rt:list-length` and the index fixing
helper; and `COERCE`, `LENGTH`, `CHAR` and `SUBSEQ` against the source
completions on strings and on other data, including dotted tails,
out-of-range and noninteger indices, negative indices, a nondefault
result type, a NIL end, and zero padding. Any use of a saturated boxed
count is either equivalent for the lookup or accompanied by an actual
size bound for the requested result. Each loop progresses, each byte
or cons write has a stated extent, and a movable input is reloaded
from its root slot.

The package is complete when it supplies all four call contracts with
their resource cases. The view and length lemmas, or a fully
certified string or list path, are useful on their own.
`sh compiler/proofs/sequences/certify.sh` certifies it.

### P12. Symbols, package operations and interning

The books are in `compiler/proofs/symbols/`. They build on `machine`,
`values`, `heap` and `interfaces`, and assume static package and
bucket agreement, allocation, stack growth, byte equality and empty
string construction.

The goal is `rt:symbol-view`, `rt:package-row`, `rt:find-package` and
`rt:package-query` with their actual input, output and register
contracts, and `SYMBOL-NAME`, `SYMBOL-PACKAGE-NAME`, `PKG-IMPORTS`,
`PKG-WITNESS` and `INTERN-IN-PACKAGE-OF-SYMBOL` against
`core-primitive`, covering hidden and absent packages, the defaults
on nonstrings and nonsymbols, and interning through imports. For
dynamic table lookup, insertion and doubling, the masked hash matches
the corresponding static or dynamic key, each bucket chain
terminates, the entry count and mask describe the vector, and every
old binding survives rehashing. A new home symbol preserves
uniqueness, and a published root reaches every dynamic symbol.

The package is complete when it gives all five public contracts and a
table invariant preserved by insertion and collection. Certified
package queries, lookup, or one rehash loop are useful on their own.
`sh compiler/proofs/symbols/certify.sh` certifies it.
