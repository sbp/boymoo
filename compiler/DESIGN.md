# A compiler of many passes

This directory holds the many-pass compiler for ACL2 Core, written in ACL2 Core like the single-pass compiler of `compiler/single/`. It lowers a program through a series of small passes, each from one intermediate language to the next. Every pass up to the last few is independent of the machine, and only the last passes, from the lowest intermediate language into A64 instructions, know the target. The design follows two published compilers: QBE, a compiler back end whose intermediate language is in static single assignment (SSA) form, and Chez Scheme, whose compiler is a long series of "nanopasses" over a sequence of precisely defined languages. The single-pass compiler is the reference, both for the values that compiled programs give and for their speed and memory.

This compiler shares with the single-pass compiler everything around its code generator: the reader (`read.lisp`), the index (`index.lisp`), the data builder (`data.lisp`), the assembler (`a64.lisp`) and the writers of executables (`macos.lisp`, `sha256.lisp`, `linux.lisp`). In place of that compiler's `gen.lisp` and `compile.lisp` (`compiler/single/`) it has the passes below, and it has a runtime of its own, `runtime.lisp`, with the routines and contracts of the single-pass compiler's runtime and another collector (section 5). An executable it writes has the same input, output, exit statuses, data representation and static block as one written by the single-pass compiler (`compiler/README.md`).

## 1. What QBE and Chez Scheme do

**QBE** (`main.c`, the function `func`) runs each function through: ABI lowering of parameters (`abi0`); building the control flow graph and its uses (`fillcfg`, `filluse`); promoting stack slots to temporaries (`promote`); building SSA form with phi nodes (`ssa`); alias analysis and load forwarding (`fillalias`, `loadopt`); coalescing stack slots (`coalesce`); global value numbering with constant folding (`gvn`, with `fold.c`); simplifying the graph (`simplcfg`); global code motion (`gcm`); if-conversion to conditional selects (`ifconvert`); ABI lowering of calls and returns (`abi1`); simplification (`simpl`); instruction selection for the target (`isel`); liveness (`filllive`); loop depth and spill costs (`fillloop`, `fillcost`); spilling, which bounds the number of live temporaries by the number of registers (`spill`); register assignment on SSA form with hints and parallel moves (`rega`); jump simplification (`simpljmp`); and emission (`emitfn`). Everything up to `abi1` is the same for every target; `isel`, the register file and `emit` are per target (`arm64/`).

**Chez Scheme** (`s/cpnanopass.ss`, `s/cpprim.ss`, `s/np-languages.ss`) defines about thirty languages, `L1` to `L16`, and a pass between each pair. The passes that matter here: `cp0`, a source-level optimiser that inlines, folds constants and removes dead bindings; `np-recognize-let`; `np-convert-closures` and its optimisation of direct calls; `np-simplify-if`; `np-expand-primitives`, which turns each primitive into the machine-level operations on the data representation (tag tests, loads, inline allocation) with calls to library routines for the slow cases; `np-remove-complex-opera*`, which names every intermediate result (A-normal form); `np-impose-calling-conventions`, which makes registers, frames and the return address explicit; `np-expose-allocation-pointer`; `np-expose-basic-blocks`; `np-allocate-registers`, which computes liveness, places the variables that live across calls in frame locations (which the collector reads through live masks at each return point), selects instructions for the target, and colours the rest into registers; and assembly. Chez makes every register caller-saved, so that a variable that lives across a non-tail call is in the frame, where the collector can find and move what it refers to.

**What is taken.** ACL2 Core has no closures, no assignment and no first-class functions, so Chez's passes for closures, assignments, multiple values and continuations have no work to do. What remains of both designs: a source-level simplifier (`cp0`), primitive expansion against the data representation (`np-expand-primitives`), SSA form with value numbering, folding and simplification of the graph (QBE), a calling convention in which every register is caller-saved and data that live across a call that may collect are kept in a frame the collector reads (Chez), and liveness, spilling, register assignment and emission per target (QBE `isel`, `spill`, `rega`, `emit`).

## 2. The passes

| Pass | Book | From | To | Depends on the target |
|---|---|---|---|---|
| P0 | `read`, `index`, `data` (shared with the single-pass compiler) | program text | lines, definitions, constants | no |
| P1 | `resolve.lisp` | L0 | L1 | no |
| P2 | `simplify.lisp` | L1 | L1 | no |
| P3 | `lower.lisp` | L1 | QIR-A | no |
| P4 | `expand.lisp` | QIR-A | QIR-M | no (only the data representation) |
| P5 | `opt.lisp` | QIR-M | QIR-M | no |
| P6 | `abi.lisp` | QIR-M | QIR-L | no (only the number of argument registers) |
| P7 | `isel.lisp` | QIR-L | MIR | A64 |
| P8 | `rega.lisp` | MIR | MIR | A64 |
| P9 | `emit.lisp` | MIR | assembly items | A64 |
| | `compile.lisp` | | | `COMPILE-TEXT`, which joins them |

`qir.lisp` holds what the passes on QIR share: recognisers of well-formed QIR-A, QIR-M and QIR-L, a printer, the table of runtime routines (which may collect), and the maps from labels to blocks. Passes P2 and P5 can each be switched off without changing what a program computes; each must give a program that computes the same values as its input.

## 3. The languages

All names are strings, as `read.lisp` gives them (`"ACL2::FOO"`). A **datum word** is the 64-bit encoding of `compiler/README.md`, "The data". A constant of the program is the value that `data-build` gives for its text: a natural number, the word, or a cons whose `cdr` is the integer `n` of an immediate integer, whose word is `2n + 1` modulo 2<sup>64</sup> (see `gen-load-datum` in `compiler/single/gen.lisp`). The passes below write every constant as a word.

### L0

The definitions as `index-lines` gives them: `(NAME FORMALS BODY)`, where `FORMALS` is a list of strings or `"COMMON-LISP::NIL"`, and a term is a variable (a string), `("COMMON-LISP::QUOTE" TEXT)`, `(HEAD ARG ...)` with `HEAD` a name, or `(("COMMON-LISP::LAMBDA" FORMALS BODY) ARG ...)`. A lambda body refers only to the lambda's formals.

### L1, resolved terms

P1 resolves every head through the attachments, checks arities as the single-pass compiler's `gen.lisp` does, replaces each constant by its word, takes the logical argument of `(RETURN-LAST 'MBE1-RAW EXEC LOGIC)` as `gen.lisp` does, and renames every variable to a natural number, so that each binding in a definition has a number of its own.

```
e ::= (:var V)                    V a natural number, bound once in its definition
    | (:const W)                  W a datum word
    | (:if E1 E2 E3)              E2 when E1 is not NIL, else E3
    | (:let (V1 ... Vn) (E1 ... En) E)
                                  E1 ... En evaluated in order, then E with Vi bound to the value of Ei;
                                  E may refer to V1 ... Vn and to any variable in scope around the let
                                  (P1 gives closed lets, as ACL2 does; P2 may open them, which the
                                  distinct names make safe)
    | (:call F (E1 ... En))       a function of the program with a definition, n its arity
    | (:prim P (E1 ... En))       P the name of a primitive or a function of the prelude (index.lisp, *primitives* and *jets*)
    | (:undef W (E1 ... En))      a function with no definition and no attachment, W the word of its symbol:
                                  the arguments are evaluated, then the program stops with status 1
d ::= (NAME (V1 ... Vn) E)        the formals are numbered 0 to n - 1; each lambda formal
                                  takes the next number not yet used in the definition
```

Arguments are evaluated from left to right. A program in L1 is the list of its definitions; the entry's definition is made by the driver as `compile-entry-definitions` does in `compiler/single/compile.lisp`.

### QIR-A, the abstract SSA language

```
program  ::= (fn ...)
fn       ::= (:fn NAME PARAMS BLOCKS)
PARAMS   ::= list of data temporaries
BLOCKS   ::= list of blocks; the first is the entry block, which has no predecessors and no phis
block    ::= (LABEL PHIS INSTS JUMP)        LABEL a natural number, distinct within the function
PHIS     ::= list of (TEMP ARGS), ARGS a list of (PRED-LABEL . OPERAND), one for each predecessor
INSTS    ::= list of (DEST OP OPERAND ...)  DEST a temporary or NIL
operand  ::= (:d . N)    a data temporary: it holds a datum word whenever the collector can see it
           | (:w . N)    a word temporary: any 64-bit word, never seen by the collector
           | (:k . W)    the constant word W, a natural number below 2^64 (every pass writes constants so)
```

The number `N` identifies a temporary within its function; `(:d . N)` and `(:w . N)` never both occur. Every temporary is assigned exactly once, by a parameter, a phi or an instruction, and its definition dominates each use (in a phi, the use is at the end of the predecessor). Further, as `qir.lisp` checks:

1. the two targets of `:if` and `:jnz` differ, so that the predecessors of a block are distinct and a phi has one argument for each;
2. every block is reachable from the entry block;
3. any instruction may have `NIL` as its destination;
4. `:copy`, `:sel` and `:ld` may define a temporary of either class; the word operations, comparisons and `:ldb` define word temporaries; `:cons`, `:call` and `:rt` define data temporaries; the arguments of `:call`, `:tail`, `:ret`, `:cons`, `:rt` and `:if`, and the arguments of the phi of a data temporary, are data.

| Instruction | Meaning |
|---|---|
| `(T :copy A)` | the value of `A` |
| `(T :prim P A ...)` | the primitive or prelude function `P` applied to the data |
| `(T :call F A ...)` | the function `F` of the program applied to the data |

| Jump | Meaning |
|---|---|
| `(:jmp L)` | go to block `L` |
| `(:if A L1 L0)` | go to `L1` when the datum `A` is not `NIL` (the word 34), else to `L0` |
| `(:ret A)` | return the datum `A` |
| `(:tail F A ...)` | return the value of the call |
| `(:undef W)` | stop with status 1 for the function whose symbol has the word `W` |

P3 turns a call of a function by itself in tail position into a jump to a loop header, a block whose phis take the parameters.

### QIR-M, the machine-level SSA language

P4 replaces each `:prim` by operations on words, following the data representation of `compiler/README.md`; QIR-M has no `:prim`. It adds:

| Instruction | Meaning |
|---|---|
| `(T :add A B)`, `:sub`, `:mul`, `:and`, `:or`, `:xor` | modulo 2<sup>64</sup> |
| `(T :shl A B)`, `:shr`, `:sar` | shifts by `B` modulo 64; `:shr` logical, `:sar` arithmetic |
| `(T :ceq A B)`, `:cne`, `:cslt`, `:csle`, `:csgt`, `:csge`, `:cult`, `:cule`, `:cugt`, `:cuge` | 1 if the comparison holds, else 0, signed (`s`) or unsigned (`u`) |
| `(T :ovadd A B)`, `(T :ovsub A B)` | 1 if `A + B` or `A - B` overflows as a signed 64-bit integer, else 0 |
| `(T :sel C A B)` | `A` if the word `C` is not 0, else `B` |
| `(T :ld A B)` | the word at heap base + `A` + `B`, where `A` is a datum (a data temporary or a constant), its tag included, and `B` a constant or a word temporary: the `car` of a cons `X` is `(:ld X (:k . 0))`, its `cdr` `(:ld X (:k . 8))`, the header of an object `X` with a header `(:ld X (:k . 18446744073709551614))` |
| `(T :ldb A B)` | the byte at that address, as a word from 0 to 255 |
| `(T :cons A B)` | a new cons of the data `A` and `B`; may collect |
| `(T :rt R A ...)` | the runtime routine `R`, a label such as `"prim:COMMON-LISP::EQUAL"`, with its arguments in order and its result |

and the jump `(:jnz A L1 L0)`: go to `L1` when the word `A` is not 0, else to `L0`. QIR-M has no `:if`: P4 replaces each by a `:jnz` of the comparison of its datum with `NIL`.

A temporary's class is fixed by its definition: a `:ld` of a field that holds a datum, a `:copy` of a word that is known to be a datum (for example the result of an addition of two immediate integers that did not overflow), and the results of `:cons`, `:call` and of routines that give data define data temporaries; every other result is a word. No word temporary may hold an address of the machine, so that nothing but the heap base needs to change when the collector moves objects.

**May collect**: `:call`, `:cons`, and `:rt` of a routine that allocates; a `:tail` leaves the frame before the callee starts, and a prologue cannot collect (`compiler/README.md`, "The runtime"; the table is in `qir.lisp`).

### QIR-L, the language with frames

P6 takes QIR-M out of SSA form (each phi becomes a parallel copy at the end of each predecessor, after splitting critical edges) and makes the collector's frame explicit. A function becomes `(:fn NAME PARAMS BLOCKS NSLOTS)`, blocks have no phis, a temporary may be assigned more than once, and there are two more instructions:

| Instruction | Meaning |
|---|---|
| `(NIL :spill I A)` | store the datum `A` in slot `I` of the frame on the value stack |
| `(T :reload I)` | the datum in slot `I` |

The invariant: across every instruction that may collect, no data temporary is live except those that are spilled before it and reloaded after it. Word temporaries live across such an instruction are kept by the back end in places the collector does not read.

### MIR and the back end

P7 to P9 belong to the target. MIR is A64 instructions over virtual registers, close to the assembly items of `compiler/README.md`, "The assembly language". P8 computes liveness and assigns registers by linear scan over the blocks in reverse post-order, with spill slots; P9 writes the prologue and epilogue, resolves parallel moves, lays out blocks and writes assembly items. `README.md`, "MIR", gives MIR exactly.

## 4. The calling convention of compiled functions

| | |
|---|---|
| Arguments | the first eight in `x0` to `x7`; the rest in the words below `x25` on entry, pushed by the caller in order, popped by the callee on return |
| Result | `x0` |
| Kept by a call | `x23` to `x28` (`compiler/README.md`, "The runtime"), `sp`; every other register may change |
| Value-stack frame | `NSLOTS` words above the arguments on the value stack, allocated in the prologue with the check against `x24` (`rt:grow`), and set to a word the collector leaves alone before anything can collect |
| Machine stack | 16 bytes for the link when the function calls, with the check against `x23` (`rt:deep`) |
| Tail call | arguments into place, frame removed, jump |

The runtime's routines keep `x19` to `x22` (`compiler/README.md`, "The runtime"), so a word or datum in one of those registers survives a call of a routine that does not allocate. `rt:entry` is a small adapter that takes the argument from the value stack, calls the entry function and returns to `rt:start` with every register that `rt:start` relies on as it was.

The rule of `compiler/README.md` holds without change: the only natives are the 32 primitives and the five functions of the prelude, chosen by name. No pass may recognise a function of a program by its name or by the shape of its definition and replace it with other code. Inlining a definition into its callers, by a rule that applies to every definition alike, is a transformation of the program and is allowed.

## 4a. Routines of the runtime written in QIR

`rt-qir.lisp` writes three routines of the runtime as functions of QIR-M. `rt-qir:LENGTH`, `rt-qir:CHAR` and `rt-qir:EQUAL`, with its helper `rt-qir:EQUAL-ATOM`, compute what `jet:COMMON-LISP::LENGTH`, `jet:COMMON-LISP::CHAR` and `prim:COMMON-LISP::EQUAL` compute, for every datum. The driver adds `(RT-QIR-FUNCTIONS)` to the program after P4, and P5 to P9 compile them as they compile the program's functions. Their names have no `::`, so no function of a program has one of them.

They obey the contract of a routine (`compiler/README.md`, "The runtime"), not that of a compiled function (section 4). They take their arguments in `x0` onwards and give their result in `x0`. They keep `x19` to `x23`, `x25`, `x28`, `x29` and `sp`, change only `x0` to `x17`, `x24` and the flags, and do not allocate. The table of routines in `qir.lisp` lists them with that contract. P8 allocates their registers without `x19` to `x22` and `x29`, and P9 gives each the label of its name as well as `(:fn NAME)`. P4's entry `EXPAND-PROGRAM` calls them with `:rt` in the slow paths of `EQUAL`, `LENGTH` and `CHAR`, so P6 and P8 treat those calls as calls of routines that do not allocate. Values may then stay in `x19` to `x22` across such a call. A call from one of these functions to another, such as the comparison of two CARs in `rt-qir:EQUAL`, is a `:call`. The hand-written routines stay in `runtime.lisp`, where the runtime itself calls them.

`rt-qir:EQUAL` decides the cases that need no traversal itself. It follows the CDRs of two lists in a loop and decides each pair of different CARs that are atoms. Two objects with headers go to `rt-qir:EQUAL-ATOM`, which compares strings and integers byte by byte and decides symbols, and which gives fractions, complex rationals and vectors to the hand-written routine. At the first pair of CARs that are both conses, the rest of the two lists goes to the hand-written routine, which keeps its pending comparisons on the value stack. No function among them calls itself, directly or not. P9 therefore leaves out their checks of the machine stack, and their frames, tens of bytes, use the margin below `x23` as the routines do. A comparison stops only where the routine's would. Two distinct chains of 4,300,000 nested CARs compare as they do under the single-pass compiler, and `rt-qir:EQUAL` under 4,193,277 live recursive frames succeeds and fails at the same depths as the hand-written routine.

Measured on 2026-11-27 with `/usr/bin/time -l` (instructions retired), the checker's library check takes 106.7 G instructions, against 107.4 G when the compiler calls the hand-written routines in those slow paths. The single-pass compiler, compiled both ways and running on its own input, `build/compiler/single/compiler.input`, takes 2.850 G against 2.895 G. With the calls made by `:call` under the compiled-function convention, the two cost 8.7% and 2.9% more than with the hand-written routines. Every value live across such a call is kept in a frame slot for its whole life, even when the slow path is not taken.

## 5. Memory

The collector of the single-pass compiler's runtime (`compiler/single/runtime.lisp`) copies between two spaces, with a budget of twice the bytes that survived. The data of ACL2 Core are never changed after they are made, so an object can refer only to objects older than itself. The one exception in the runtime is the table of symbols made while the program runs (the word at offset 24 of the static block): interning writes into its vector, and doubling the table (`rt:intern-rehash-entry`) rewrites the link of every entry, so that an old entry can come to refer to a young one. This makes a generational collector cheap: a collection of a young generation needs no write barrier, only the value stack and that table, scanned whole, as roots (or a full collection after each doubling). The candidates, in order of the work they need:

1. A tighter policy for the budget, measured against the time it costs.
2. A nursery of fixed size, whose survivors are copied into an old space that grows by bump allocation, with a full collection of the old space when it has doubled.
3. A full collection by sliding compaction in place, so that the old space needs no second space.

Each is judged by the peak of resident memory and the time of the benchmarks of section 7. The runtime of this compiler, `runtime.lisp`, takes a form of the second, whose nursery grows with the old generation (`README.md`, "The runtime").

## 6. Proofs

Every pass is a function in ACL2's logic, so a theorem can be stated about the code that runs. For each pass the aim is: a semantics of its source and target languages as evaluators with fuel (L1 has `compiler/model/core.lisp` as its reference), a recogniser of well-formed programs of each language, a theorem that the pass maps well-formed programs to well-formed programs, and a theorem that the pass preserves what a program computes. Where the second is out of reach, a checker of the pass's output that is proved sound, run by the compiler on every output, takes its place (translation validation). The proofs are in `compiler/proofs/`, with a report of what each states and what it does not.

## 7. Benchmarks

`compiler/bench/` compares executables written by the single-pass compiler with those written by this compiler from the same input, for elapsed time and peak resident memory under `/usr/bin/time -l`, and requires the same output byte for byte: the single-pass compiler compiling itself, the compiled checker on the library check of `compiler/README.md`, and the programs of `runner/bench/`.
