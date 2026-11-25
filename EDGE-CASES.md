# Edge cases

This document lists every place found where what ACL2 8.7, the program, does goes beyond, falls short of, or differs from what ACL2's axioms say, and every place where a careful reader would fear that the two part. For each place it says what ACL2 Core does, the language of this repository that [`spec/language.md`](spec/language.md) defines.

ACL2 is the definition of ACL2. Where ACL2 Core differs from ACL2, the entry gives the reason and says whether the difference can be removed. A difference that waits on a decision is listed under "Undecided" in [`PLAN.md`](PLAN.md).

Every example was run in ACL2 8.7. One command confirms every entry, from the root of the repository:

```
sh checks/run.sh
```

Its line `checks/expected/edge.txt is what ACL2 says on each entry of EDGE-CASES.md` comes from [`checks/edge.lsp`](checks/edge.lsp), which writes one line for each fact below. The label of each line begins with the number of its entry, except that the lines `value`, `no-value`, `read` and `no-read` name the call or the text instead. Some entries also rest on lines of `checks/expected/facts.txt`, which [`checks/facts.lsp`](checks/facts.lsp) writes. The checks were last run on 2026-11-25, with ACL2 8.7 built on SBCL 2.5.5, and printed `all checks passed`.

## Terms

- **Axiom.** A formula that ACL2 takes as true without proof. ACL2's own axioms are the 84 `defaxiom` events of its source file `axioms.lisp`. Beside them stand its **principles**: the rules by which a definition, a constraint, a choice or an induction adds to what is true. Together these are what this document calls "the axioms".
- **Ground theory.** What every checker holds before it reads anything: ACL2's axioms, its 32 primitive functions, 37 of its definitions, 41 facts that ACL2 proves although no axiom states them, and the 23 clauses about `acl2-count` that ACL2's prover takes as true with no proof (entry 9.6). It is the file [`spec/ground.txt`](spec/ground.txt) ([`spec/logic.md`](spec/logic.md), section 3).
- **Primitive.** One of the 32 functions with no definition, such as `car` and `binary-+`, whose meaning only the axioms give.
- **Completion.** The value that an axiom gives to a primitive on arguments it was not meant for, such as `(car 7)`. ACL2's axioms of this kind are named `completion-of-...`.
- **The Lisp under ACL2.** ACL2 is a Common Lisp program. Each function it defines is also compiled as Common Lisp code, which ACL2 runs to compute values. ACL2's documentation calls this "raw Lisp". For some functions that code is not the function's definition.
- **Evaluator.** The part of ACL2 that computes the value of a term on constants: at its top level, in `defconst`, and inside a proof. It uses either the Common Lisp code of a function or a slower version that follows the definition and checks guards, which ACL2 calls the executable counterpart.
- **Guard.** A condition that ACL2 asks of a function's arguments before it runs the function's Common Lisp code. A guard is no part of the logic. **Guard checking** is the setting that says what ACL2 does when a guard fails; it is one of `t` (the default), `:all`, `:nowarn`, `nil` and `:none` (entry 2.4).
- **Logic mode and program mode.** A function in logic mode has a definition that the logic holds as an axiom. A function in program mode can only be run; ACL2 proves nothing about it.
- **Constrained function.** A function introduced by `encapsulate` with no definition: the logic knows only the formulas of its **constraint**. A function introduced by `partial-encapsulate` has **unknown constraints**: ACL2 records the mark `:unknown-constraints` instead of formulas, and its Common Lisp code says what it does.
- **Attachment.** A function that ACL2 runs in place of a constrained function when it evaluates a term at its top level, set by `defattach`. An attachment is no part of the logic.
- **Single-threaded object.** An object, such as ACL2's `state`, of which only one copy exists while ACL2 runs, and which the logic treats as a list.
- **Hidden package.** A package that reaches ACL2's world only because a book that was included locally declared it. ACL2 keeps it, so that its symbols can stand in events that remain, but states no axiom about it and treats its name as that of no package.
- **Trust tag.** A name declared by `defttag`, which lets the events after it do things that the logic does not cover, such as changing the Lisp under ACL2.
- **Statement, library, checker, runner, program text.** A statement is one line of ACL2 Core that says what an event of a book adds. The library is the statements of ACL2's own built-in functions. A checker checks proofs of statements ([`spec/logic.md`](spec/logic.md)). A runner computes the value of a term with no variables, from program text: definitions and attachments ([`spec/language.md`](spec/language.md), section 4).

## How an entry reads

Each entry has five parts.

- **The axioms**: what they say or leave open, with the axiom or the section of the specification.
- **ACL2**: what the program does.
- **Example**: the smallest input that shows it, and exactly what ACL2 8.7 answers. Values are written as ACL2 prints them; a character with code `n` is written `(code-char n)`.
- **ACL2 Core**: what a checker and a runner do, and where the specification says so; if they differ from ACL2, why, and whether that can change.
- **Check**: the lines that confirm the entry. "Lines 2.4" means the lines of `checks/expected/edge.txt` whose label begins with `2.4`.

## All entries

In the third column, "Yes" means that ACL2 Core gives ACL2's answer; "Yes, and asks more" that ACL2 Core requires a proof where ACL2 did not; "No" that it cannot follow, for the reason given; "Not yet" that it can follow and a decision is waited on; and "No counterpart" that no input of ACL2 Core corresponds.

| Entry | Kind | ACL2 Core follows ACL2 |
|---|---|---|
| 1.1 `bad-atom<=` on data | 1 | Yes |
| 1.2 The imports of `COMMON-LISP` | 1 | Yes |
| 1.3 `intern-in-package-of-symbol` at a symbol of a hidden package | 1 | Yes |
| 1.4 The case of the characters that are not standard | 1 | Not yet |
| 1.5 Double-floats | 1 | No |
| 2.1 A constrained function with no attachment | 2 | Yes |
| 2.2 `hard-error`, `illegal` and `er hard` | 2 | Yes |
| 2.3 Functions that are not executable | 2 | Yes |
| 2.4 Guard violations under each setting of guard checking | 2 | Yes, as under `:none` |
| 2.5 The executable half of an `mbe`, and `do$` | 2 | Not yet |
| 2.6 Exhaustion of the stack | 2 | Yes, in kind |
| 2.7 Single-threaded objects at run time | 2 | No counterpart |
| 2.8 `pkg-imports` and `pkg-witness` on a name that is no package | 2 | Yes |
| 2.9 `symbol-package-name` at a symbol of a hidden package | 2 | Yes |
| 2.10 A shift by a count that the Lisp under ACL2 cannot make | 2 | Yes, in kind, without `-j`; with it, the axioms' value |
| 2.11 `nthcdr` by a count far beyond a list that does not end in `nil` | 2 | Yes, in kind, without `-j`; with it, the axioms' value |
| 3.1 Attachments | 3 | Yes |
| 3.2 `apply$` and warrants | 3 | No |
| 3.3 Functions whose Common Lisp code is not their definition | 3 | Yes, except 1.4, 1.5 and 3.2 |
| 3.4 State, the oracle, time, random numbers and the host | 3 | No counterpart |
| 3.5 Memoization | 3 | Yes |
| 4.1 The completions of the primitives | 4 | Yes |
| 4.2 Library functions that inherit a completion | 4 | Yes |
| 5.1 Exactly 256 characters | 5 | Yes |
| 5.2 Numbers in ACL2's reader | 5 | No counterpart |
| 5.3 Characters and strings in ACL2's reader | 5 | No counterpart |
| 5.4 Symbols in ACL2's reader | 5 | No counterpart |
| 5.5 What ACL2's reader refuses | 5 | No counterpart |
| 5.6 Reading that depends on the host Lisp | 5 | No counterpart |
| 5.7 Bad atoms | 5 | Yes |
| 6.1 Names | 6 | Yes, except names the host Lisp uses and untouchable functions: not yet |
| 6.2 The termination machine and ruler-extenders | 6 | Yes |
| 6.3 Measures that ACL2 guesses | 6 | Yes |
| 6.4 Well-founded relations other than `o<` | 6 | Yes |
| 6.5 The body ACL2 stores | 6 | Yes |
| 6.6 Definitions that join the constraint of an `encapsulate` | 6 | Yes |
| 6.7 Where the constraint of an `encapsulate` is stored | 6 | Yes |
| 6.8 `defchoose` with `:strengthen` | 6 | Yes |
| 6.9 `defun-sk` | 6 | Yes |
| 6.10 Redundant events | 6 | Yes |
| 6.11 `local` | 6 | Yes |
| 6.12 Tests that leave nothing in a statement | 6 | No |
| 6.13 Single-threaded objects in the logic | 6 | Yes |
| 6.14 `loop$` and lambda objects | 6 | Not yet |
| 7.1 The packages ACL2 starts with | 7 | Not yet |
| 7.2 The names of packages | 7 | Yes, except for the host Lisp: not yet |
| 7.3 Imports are sorted and have no repeats | 7 | Yes |
| 7.4 `defpkg` only at the top level | 7 | Yes |
| 7.5 A symbol written with one package that belongs to another | 7 | Yes |
| 7.6 Hidden packages | 7 | Yes |
| 8.1 `defaxiom` | 8 | Yes |
| 8.2 `skip-proofs` | 8 | Yes, and asks more |
| 8.3 Books with no certificate | 8 | Yes, and asks more |
| 8.4 Trust tags, `progn!` and raw Lisp | 8 | Yes, and asks more |
| 8.5 Redefinition | 8 | Yes, and asks more |
| 8.6 `make-event` | 8 | Yes |
| 9.1 Induction up to ε<sub>0</sub> | 9 | Yes |
| 9.2 The definitional principle | 9 | Yes |
| 9.3 Functional instantiation | 9 | No rule; the same theorems |
| 9.4 Choice | 9 | Yes |
| 9.5 Proof by evaluation | 9 | Yes, except 1.4, 1.5 and 8.4 |
| 9.6 The built-in clauses about `acl2-count` | 9 | Yes |
| 10.1 `mbe` in program mode | 10 | Yes |
| 10.2 Primitives outside their guards in program mode | 10 | Yes, as under `:none` |
| 10.3 Functions in program mode with Common Lisp code only | 10 | No |

The kinds, with the number of entries of each: 1, the axioms leave a value open and ACL2 computes one (5); 2, the axioms give a value and ACL2 computes none (11); 3, ACL2 computes a value that the axioms do not prove (5); 4, the values the axioms give to arguments outside the guards (2); 5, data (7); 6, admission, where ACL2's tests are not the logic's (14); 7, packages (6); 8, ways a session leaves the axioms (6); 9, where the logic is not a set of axioms (6); 10, program mode (3). That is 65 entries.

## 1. The axioms leave a value open and ACL2 computes one

### 1.1 `bad-atom<=` on data

- **The axioms.** `booleanp-bad-atom<=`, `bad-atom<=-antisymmetric`, `bad-atom<=-transitive` and `bad-atom<=-total` say that `bad-atom<=` gives `T` or `NIL` and order the objects that are not data (entry 5.7). On two data they say nothing.
- **ACL2.** Its evaluator gives `NIL` on any two data, and its prover proves theorems by that evaluation.
- **Example.** `(bad-atom<= 1 2)` gives `NIL`. ACL2 proves `(equal (bad-atom<= 1 2) nil)`.
- **ACL2 Core.** Computes `NIL` ([`spec/language.md`](spec/language.md), sections 3 and 4). [`spec/logic.md`](spec/logic.md), sections 1 and 10, names this as one of the facts that stand beside ACL2's axioms.
- **Check.** Lines 1.1; the lines `value` for `bad-atom<=` of `checks/expected/facts.txt`.

### 1.2 The imports of `COMMON-LISP`

- **The axioms.** Four `defaxiom` events give the imports of `ACL2`, `KEYWORD`, `ACL2-INPUT-CHANNEL` and `ACL2-OUTPUT-CHANNEL`. None gives those of `COMMON-LISP`, so the axioms do not say what `(intern-in-package-of-symbol "BM-NEW" 'car)` is.
- **ACL2.** Its source says that it "pretends that no symbols are imported" into `COMMON-LISP`. It computes with that and proves theorems by it.
- **Example.** `(pkg-imports "COMMON-LISP")` gives `NIL`, and `(intern-in-package-of-symbol "BM-NEW" 'car)` gives `COMMON-LISP::BM-NEW`. ACL2 proves `(equal (pkg-imports "COMMON-LISP") nil)`.
- **ACL2 Core.** The ground theory states it as its fifth `package` line ([`spec/logic.md`](spec/logic.md), sections 3 and 10).
- **Check.** Lines 1.2.

### 1.3 `intern-in-package-of-symbol` at a symbol of a hidden package

- **The axioms.** ACL2 states no axiom about the imports of a hidden package (entry 7.6), so the axiom `symbol-package-name-intern-in-package-of-symbol` cannot be applied at one of its symbols.
- **ACL2.** Its evaluator interns from the imports it keeps for the package, and its prover proves theorems by it. A function defined in a book can return a symbol of a hidden package.
- **Example.** `build/edge-hidden.lisp` defines `bm-hidden-symbol`, whose value is the symbol `FOO` of the hidden package `BM-HIDDEN`, which imports `COMMON-LISP::CAR` and `ACL2::BM-HIDDEN-IMPORT`. `(intern-in-package-of-symbol "CAR" (bm-hidden-symbol))` gives `COMMON-LISP::CAR`; with `"BM-HIDDEN-IMPORT"` it gives `ACL2::BM-HIDDEN-IMPORT`; the symbol made from `"NEW"` has the name `"NEW"`. ACL2 proves `(equal (intern-in-package-of-symbol "CAR" (bm-hidden-symbol)) 'car)`.
- **ACL2 Core.** Computes the same, from the imports that the `hidden-package` statement declares ([`spec/language.md`](spec/language.md), section 3; [`spec/logic.md`](spec/logic.md), section 6). The argument of `spec/logic.md`, section 6, already lets every package of an input, the hidden ones among them, import what its statement declares.
- **Check.** Lines 1.3.

### 1.4 The case of the characters that are not standard

- **The axioms.** ACL2 defines `char-upcase`, `char-downcase`, `upper-case-p`, `lower-case-p` and `alpha-char-p` by a table on the 96 standard characters. On the other 160 it calls five functions, `char-upcase-non-standard` and its siblings, introduced by `partial-encapsulate`: their constraints are unknown.
- **ACL2.** It runs the Common Lisp functions of the same names, those of the host. Its prover evaluates the five functions in the same way and proves theorems by it. ACL2 starts with 44 functions with unknown constraints; the others are those of entry 1.5, the two behind `apply$` (entry 3.2), and functions of ACL2's own machinery, such as `magic-ev-fncall` and `canonical-pathname`.
- **Example.** `(char-upcase (code-char 233))` gives `(code-char 201)`, `(char-downcase (code-char 201))` gives `(code-char 233)`, and `(upper-case-p (code-char 201))` gives `T`. ACL2 proves `(equal (char-upcase (code-char 233)) (code-char 201))`. The constraint it keeps is `(:unknown-constraints ...)`, on `alpha-char-p-non-standard`, and no function is attached.
- **ACL2 Core.** A checker cannot prove the theorem: the five functions are `constrain` statements whose formulas are those ACL2 states, and a checker never runs code. A runner stops at a call of them, as at any function with no definition and no attachment ([`spec/language.md`](spec/language.md), section 4). This can be followed: the five functions on the 160 characters are 800 values, each of which ACL2 computes and proves as the two theorems above show, and the library could hold them as theorems. Whether it should is undecided (`PLAN.md`). They depend on the Lisp under ACL2.
- **Check.** Lines 1.4, among them the lines `count` and `stored` that list the 44 functions.

### 1.5 Double-floats

- **The axioms.** ACL2 8.7 represents a double-float in the logic as a rational. `to-df` rounds a rational to one; it is defined as `constrained-to-df`, whose constraints are unknown, and so are those of the functions behind `df-sqrt`, `df-sin` and the rest. The axioms do not say which rational `(to-df 1/3)` is.
- **ACL2.** It computes with the floating-point arithmetic of the Lisp under it, and proves theorems by those computations.
- **Example.** `(to-dfp 1/3)` gives `6004799503160661/18014398509481984`; `(to-dfp 1/10)` gives `3602879701896397/36028797018963968`; `(from-df (df-sqrt (to-df 2)))` gives `6369051672525773/4503599627370496`. ACL2 proves the first and the third as equations.
- **ACL2 Core.** Cannot follow. A checker cannot prove these theorems, and a runner stops at the constrained functions. To follow ACL2, a checker would have to trust the floating-point code of a host for infinitely many values.
- **Check.** Lines 1.5.

## 2. The axioms give a value and ACL2 computes none

### 2.1 A constrained function with no attachment

- **The axioms.** A constraint can fix a value: if `bm-three` is constrained by `(equal (bm-three x) 3)`, then `(bm-three 5)` is 3.
- **ACL2.** Its evaluator has no code for a constrained function with no attachment, and refuses.
- **Example.** `(bm-three 5)` has no value: "ACL2 cannot ev the call of non-executable function BM-THREE". ACL2 proves `(equal (bm-three 5) 3)` from the constraint.
- **ACL2 Core.** A runner stops, as ACL2 does ([`spec/language.md`](spec/language.md), section 4). A proof gets the value from the constraint.
- **Check.** Lines 2.1.

### 2.2 `hard-error`, `illegal` and `er hard`

- **The axioms.** The body ACL2 stores for `hard-error` is `'nil`, and that for `illegal` is a call of `hard-error`; `er hard` expands to `hard-error`. So each has the value `NIL`.
- **ACL2.** Their Common Lisp code reports an error and gives no value, even with guard checking `:none`.
- **Example.** `(hard-error 'bm "BM" nil)`, `(illegal 'bm "BM" nil)` and `(prog2$ (er hard 'bm "BM") 3)` have no value with guard checking `:none`. ACL2 proves `(equal (hard-error 'bm "BM" nil) nil)` and the same of `illegal`.
- **ACL2 Core.** A runner stops at them, as ACL2 does: the program text holds no definition for `hard-error` or for `throw-nonexec-error` (entry 2.3), so a call of either has no value ([`spec/language.md`](spec/language.md), section 4). A proof uses the definitions, as ACL2's prover does.
- **Check.** Lines 2.2.

### 2.3 Functions that are not executable

- **The axioms.** A function defined with `defun-nx`, or with `:non-executable t`, has the equation of its body. ACL2 stores the body wrapped as `(return-last 'progn (throw-nonexec-error 'f (cons x 'nil)) body)`, which equals `body` because `return-last` gives its last argument and `throw-nonexec-error` is defined to be `'nil`. `defun-sk` defines its function in the same way (entry 6.9).
- **ACL2.** `throw-nonexec-error` reports an error, so a call of such a function has no value.
- **Example.** After `(defun-nx bm-nx (x) (cons x x))`, `(bm-nx 3)` has no value: "ACL2 cannot ev the call of non-executable function BM-NX". ACL2 proves `(equal (bm-nx 3) '(3 . 3))`.
- **ACL2 Core.** The statement holds the body as ACL2 stores it. A runner evaluates both arguments of `return-last`, reaches `throw-nonexec-error`, which has no program text, and stops ([`spec/language.md`](spec/language.md), section 4).
- **Check.** Lines 2.3.

### 2.4 Guard violations under each setting of guard checking

- **The axioms.** `(car 7)` is `NIL` by `completion-of-car`; a function defined as `(car x)` gives the same.
- **ACL2.** With guard checking `t`, `:all` or `:nowarn`, a call whose arguments fail the guard has no value. With `nil` or `:none`, ACL2 gives the logical value.
- **Example.** `(car 7)`, `(bm-gc 7)`, where `bm-gc` is `(car x)` with the guard `(consp x)` verified, and `(bm-gu 7)`, the same with the guard not verified: no value under `t`, `:all` and `:nowarn`; `NIL` under `nil` and `:none`.
- **ACL2 Core.** Has no guards. A runner gives the logical value, as ACL2 does with guard checking `:none` ([`spec/language.md`](spec/language.md), section 4). Entries 2.5 and 10.2 are the places where ACL2 under `:none` still differs.
- **Check.** Lines 2.4.

### 2.5 The executable half of an `mbe`, and `do$`

- **The axioms.** `(mbe :logic a :exec b)` is `(return-last 'mbe1-raw b a)`, whose value is `a`. The calls inside `b` are not measured when the definition is admitted. A `do$` whose measure fails to decrease returns, by its definition, default values.
- **ACL2.** For a function whose guards are verified, ACL2 runs the Common Lisp code, and there an `mbe` is its executable half `b`. Verifying the guards proves `b` equal to `a` under the guard, but `b` may still give no value, or not terminate.
- **Example.** `bm-mbe-err` is `(mbe :logic nil :exec (hard-error ...))` with the guard `t`: it has no value under `:none` and under `t`, and ACL2 proves `(equal (bm-mbe-err 1) nil)`. `bm-mx` is `(mbe :logic x :exec (car (cons (bm-mx x) nil)))`, admitted with its guards verified: `(bm-mx 3)` exhausts the stack, and ACL2 cannot prove `(equal (bm-mx 3) 3)` because its prover tries the same evaluation; with the executable counterpart of `bm-mx` disabled it proves it. `(loop$ with x = 0 do :measure 5 (if (< 3 x) (return x) (setq x (+ x 1))))` has no value, because its measure does not decrease.
- **ACL2 Core.** A runner evaluates the logical half `a` and never `b` ([`spec/language.md`](spec/language.md), section 4), and gives `NIL`, 3 and the default values. Which half ACL2 runs depends on whether the function's guards are verified, which no statement and no line of program text carries. This can be followed if program text says which definitions have verified guards; that is undecided (`PLAN.md`). The two halves are proved equal wherever ACL2 runs `b`, so they differ only where `b` gives no value.
- **Check.** Lines 2.5.

### 2.6 Exhaustion of the stack

- **The axioms.** `bm-deep`, defined by `(if (zp n) 0 (+ 1 (bm-deep (- n 1))))`, gives `n` on every natural number.
- **ACL2.** Each call takes room on the stack of the Lisp under it, which is finite.
- **Example.** `(bm-deep 1000)` gives 1000; `(bm-deep 10000000)` has no value: "Control stack exhausted".
- **ACL2 Core.** The same in kind: a runner, too, computes with finite memory. The specification says that every run ends ([`spec/language.md`](spec/language.md), section 4), not that it fits. Exhausting the heap of the Lisp under ACL2, rather than its stack, is not among the checks.
- **Check.** Lines 2.6.

### 2.7 Single-threaded objects at run time

- **The axioms.** A single-threaded object is a list, and its functions are defined with `nth` and `update-nth`. ACL2 stores the body of `update-bm-arri` as `(update-nth-array '0 i v bm-st)`, which extends a list that is too short: ACL2 proves `(equal (update-nth 5 7 '(0 0 0)) '(0 0 0 nil nil 7))`.
- **ACL2.** At run time the object is an array of fixed size, of which only one copy exists. ACL2 checks the guards of its functions even under `:none`, it refuses a call of the function that creates the object, at its top level and in the body of a definition that can be run, though not in a theorem, it refuses a constant where the object should stand, it refuses to resize an array not declared resizable, and it refuses a call of `swap-stobjs` at its top level.
- **Example.** With `bm-st` holding an array of three integers, `(update-bm-arri 5 7 bm-st)`, `(create-bm-st)`, `(update-bm-arri 1 7 '((0 0 0) 0))` and `(resize-bm-arr 5 bm-st)` have no value under `:none`. `(defun bm-make-st () (create-bm-st))` is refused, and ACL2 proves `(equal (bm-fld (create-bm-st)) 0)`. With `bm-s1` and `bm-s2` congruent, `(mv-let (bm-s1 bm-s2) (swap-stobjs bm-s1 bm-s2) (mv bm-s1 bm-s2))` has no value, and ACL2 proves that `swap-stobjs` gives its two arguments in the other order.
- **ACL2 Core.** No term of ACL2 Core names a live object, so no input corresponds. A runner given `(update-bm-arri '1 '7 '((0 0 0) 0))` computes the logical value, where ACL2 refuses the form; to refuse it too, program text would have to say which arguments are single-threaded, which is undecided (`PLAN.md`). A checker admits a `define` whose body calls `create-bm-st`; ACL2's refusal leaves no event, as in entry 6.12.
- **Check.** Lines 2.7.

### 2.8 `pkg-imports` and `pkg-witness` on a name that is no package

- **The axioms.** `symbol-package-name-pkg-witness-name` and `symbol-name-pkg-witness` fix `(pkg-witness "")` as the symbol `ACL2::ACL2-PKG-WITNESS`. Nothing fixes `(pkg-imports "BM-NO-SUCH-PACKAGE")`.
- **ACL2.** It refuses to evaluate either function on a string that names no package it knows: the argument "is not the name of a package currently known to ACL2".
- **Example.** `(pkg-witness "")` and `(pkg-imports "BM-NO-SUCH-PACKAGE")` have no value. ACL2 proves `(equal (symbol-package-name (pkg-witness "")) "ACL2")` from the axiom.
- **ACL2 Core.** Does not compute them, and a proof may use the axioms ([`spec/language.md`](spec/language.md), section 4).
- **Check.** Lines 2.8; the lines `no-value` for these functions, and the line `accepted` for the proof, of `checks/expected/facts.txt`.

### 2.9 `symbol-package-name` at a symbol of a hidden package

- **The axioms.** A symbol has a package name; the symbol of entry 1.3 was made in the package `BM-HIDDEN`.
- **ACL2.** It refuses to evaluate `symbol-package-name` on a symbol of a hidden package, with an error of the Lisp under it: the symbol "is not in any of the packages known to ACL2". Its prover cannot prove what the package name is.
- **Example.** `(symbol-package-name (bm-hidden-symbol))` has no value, and ACL2 refuses `(equal (symbol-package-name (bm-hidden-symbol)) "BM-HIDDEN")`. `(symbol-name (bm-hidden-symbol))` gives `"FOO"`.
- **ACL2 Core.** Does not compute it ([`spec/language.md`](spec/language.md), sections 3 and 4).
- **Check.** Lines 2.9 and 1.3.

### 2.10 A shift by a count that the Lisp under ACL2 cannot make

- **The axioms.** `ash` is defined: `(ash i c)` is the floor of `i` times 2 to the power `c`, where an argument that is not an integer counts as 0. So `(ash 0 c)` is 0 for every `c`.
- **ACL2.** It computes `ash` by the code of the Lisp under it (entry 3.3), which refuses a left shift by a count too large to represent, even of 0, and ACL2 aborts.
- **Example.** ACL2 proves `(implies (integerp c) (equal (ash 0 c) 0))`. With guard checking `:none`, `(ash 0 100000000000000000000)` has no value: ACL2 8.7 aborts with the message of the Lisp under it, `can't represent result of left shift`.
- **ACL2 Core.** A checker never computes `ash`: a `compute` step evaluates only a primitive ([`spec/logic.md`](spec/logic.md), section 5), and a proof reasons about `ash` from its definition, as ACL2 proves the theorem above. A runner run without `-j` runs ACL2's definition, which makes 2 to the power `c` by one multiplication for each unit of `c`, and gives no value either. With `-j` the runner computes `ash` itself and gives 0, the value that the definition gives ([`runner/README.md`](runner/README.md), "The prelude").
- **Check.** Lines 2.10.

### 2.11 `nthcdr` by a count far beyond a list that does not end in `nil`

- **The axioms.** `nthcdr` is defined: `(nthcdr n l)` is `l` when `n` is not a positive integer, and otherwise `(nthcdr (- n 1) (cdr l))`. The `cdr` of an atom is `nil`, so it is `nil` for every `n` greater than the length of `l`, whatever atom ends `l`.
- **ACL2.** Where the guard of `nthcdr` holds, `n` a natural number and `l` a list that ends in `nil`, ACL2 computes it by the code of the Lisp under it, at once. Otherwise, with guard checking `:none`, it runs the definition (entry 2.4), one call for each unit of `n`, about 6 nanoseconds each: for a count of 2<sup>64</sup> that is some 3,500 years. `subseq` on a datum that is not a string drops its first elements with `nthcdr`, and does the same.
- **Example.** ACL2 proves `(implies (and (natp n) (< (len l) n)) (equal (nthcdr n l) nil))`. `(true-listp '(1 . 2))` is `NIL`. With guard checking `:none`, `(nthcdr (expt 2 64) '(1 2))` gives `NIL` at once, `(nthcdr 10000000 '(1 . 2))` gives `NIL` in 0.06 seconds, and `(nthcdr (expt 2 64) '(1 . 2))` and `(subseq '(1 . 2) (expt 2 64) nil)` do not finish.
- **ACL2 Core.** A checker never computes `nthcdr` or `subseq` (entry 2.10). A runner run without `-j` runs their definitions, as ACL2 does, and does not finish either. With `-j` the runner computes `subseq` itself and gives `nil`, the value that the definition gives, at once ([`runner/README.md`](runner/README.md), "The prelude"); `nthcdr` is not one of the functions of the prelude.
- **Check.** Lines 2.11. The runs that do not finish are not made; the run of 10<sup>7</sup> calls gives the rate.

## 3. ACL2 computes a value that the axioms do not prove

### 3.1 Attachments

- **The axioms.** A function introduced by `defstub` or `encapsulate` has only its constraint.
- **ACL2.** At its top level it runs the attachment in place of the function. It uses no attachment in a proof or in a `defconst`. It refuses an attachment to a function that the recognizer of a single-threaded object calls, directly or through other functions, because the attachment could make the recognizer false of the live object.
- **Example.** With `bm-s-impl`, which gives `(cons x x)`, attached to `bm-s`, `(bm-s 3)` gives `(3 . 3)`; ACL2 refuses to prove `(equal (bm-s 3) '(3 . 3))` and refuses `(defconst *bm-s* (bm-s 3))`. With the recognizer of `bm-st3` calling `bm-p`, `(defattach bm-p integerp)` is refused; the same attachment to `bm-p2`, which no recognizer calls, is accepted.
- **ACL2 Core.** A runner uses the `attach` lines of program text where ACL2 uses attachments, and a checker never reads them ([`spec/language.md`](spec/language.md), section 4). The `attach` lines are the attachments ACL2 holds, so its restrictions on them carry over.
- **Check.** Lines 3.1; the lines `run`, `plain`, `attachment` and the corresponding lines `refused` of `checks/expected/facts.txt`.

### 3.2 `apply$` and warrants

- **The axioms.** `apply$` calls `apply$-userfn` on a function that is not primitive. `apply$-userfn` is constrained; a theorem about `(apply$ 'f args)` needs the hypothesis `(warrant f)`.
- **ACL2.** At its top level it runs, in place of `apply$-userfn`, its attachment `doppelganger-apply$-userfn`, whose constraints are unknown and whose code is Common Lisp. It refuses a function with no warrant.
- **Example.** With `bm-sq` squaring its argument and warranted, `(apply$ 'bm-sq '(3))` gives 9; ACL2 refuses to prove that it equals 9 and proves it under `(warrant bm-sq)`. `(apply$ 'bm-nobadge '(3))` has no value, since `bm-nobadge` has no warrant. `(apply$ 'car '((1 . 2)))` gives 1, and ACL2 proves it, because `car` is primitive.
- **ACL2 Core.** A runner stops at `apply$-userfn`: its attachment has no program text. To give ACL2's value it would have to hold and trust the Common Lisp code beneath ACL2. This cannot be followed. The logic is the same in both: a function whose constraint ACL2 does not record is a `constrain` statement with the formulas ACL2 does hold, which may be none.
- **Check.** Lines 3.2; the lines `run`, `no-plain`, `attachment` and `constraint` for `apply$-userfn` of `checks/expected/facts.txt`.

### 3.3 Functions whose Common Lisp code is not their definition

- **The axioms.** A function in logic mode has the equation of its definition.
- **ACL2.** It lists 291 functions in logic mode as having Common Lisp code of their own. For most, such as `len`, `nth`, `floor` and `member-equal`, ACL2 relies on that code to compute the definition's value: the comment before the list in `axioms.lisp` says that such code "had better implement the logic code". For the others it does not: `hard-error` and `throw-nonexec-error` give no value (entries 2.2, 2.3); the character functions and double-floats follow the host (1.4, 1.5); the doppelgangers of `apply$` stand in for constraints (3.2); functions such as `fmt-to-comment-window`, which `cw` calls, `hons-copy` and `sleep` have effects outside the logic and give the definition's value; and functions of `state` read the host (3.4).
- **Example.** The list `*initial-logic-fns-with-raw-code*` has 291 members, among them each of the functions named here; the examples are those of the entries named.
- **ACL2 Core.** The program text holds the definitions, and gives the definition's value; the exceptions are the entries named.
- **Check.** The line `count` labelled 3.3, and the lines of the entries named.

### 3.4 State, the oracle, time, random numbers and the host

- **The axioms.** ACL2's `state` is a list, and functions such as `read-run-time`, `random$` and `read-acl2-oracle` take their values from a field of it, the oracle, about which the axioms say nothing.
- **ACL2.** At its top level there is one live `state`, and these functions take their values from the host. `wormhole-eval` gives `NIL` and changes a record that the logic does not see. `sys-call` runs a program of the host and is refused with no trust tag.
- **Example.** `(read-run-time state)` gives a rational; `(random$ 10 state)` gives a natural number below 10; `(read-acl2-oracle state)` gives the two values `NIL` and `NIL`; `(wormhole-eval 'bm-wormhole '(lambda () 7) nil)` gives `NIL`. ACL2 cannot prove `(equal (mv-nth 0 (random$ 10 state)) 0)`. `(read-run-time '(1 2))` has no value: ACL2 requires the variable `state` there. `sys-call` with no trust tag is refused (and see entry 8.4).
- **ACL2 Core.** No term of ACL2 Core names the live state, so no input corresponds. A runner given a constant in place of `state` computes the definition's value from it, where ACL2 refuses the form; this is part of the decision of entry 2.7.
- **Check.** Lines 3.4.

### 3.5 Memoization

- **The axioms.** Memoization is no part of the logic.
- **ACL2.** `memoize` makes a function remember its results.
- **Example.** `(bm-fib 25)`, a recursive Fibonacci function, gives 75025 before and after `(memoize 'bm-fib)`.
- **ACL2 Core.** No statement and no program text records memoization; it changes no value.
- **Check.** Lines 3.5.

## 4. The values that the axioms give to arguments outside the guards

### 4.1 The completions of the primitives

- **The axioms.** The 18 axioms named `completion-of-...` give each primitive a value on every object, and `<-on-others` orders the complex numbers.
- **ACL2.** With guard checking `:none` it gives these values. Several part from what a reader of Common Lisp expects.
- **Example.** With guard checking `:none`:

  | Call | Value | Why |
  |---|---|---|
  | `(car 7)`, `(cdr "ab")` | `NIL` | Not a cons. |
  | `(binary-+ 'a 1)`, `(binary-* 'a 3)`, `(unary-- 'a)` | 1, 0, 0 | A non-number is 0. |
  | `(unary-/ 0)` | 0 | The reciprocal of 0 is 0. |
  | `(< 'a 1)`, `(< 1 'a)` | `T`, `NIL` | `'a` is 0. |
  | `(< #c(1 2) #c(1 3))` | `T` | Complex numbers are ordered by real part, then imaginary part. |
  | `(char-code 'a)` | 0 | |
  | `(code-char 256)` | `(code-char 0)` | Only 0 to 255 name characters. |
  | `(complex 1 0)`, `(complex 'a 2)`, `(complex 1 #c(1 2))` | 1, `#c(0 2)`, 1 | A complex number with imaginary part 0 is rational; a part that is not rational is 0. |
  | `(numerator #c(1 2))`, `(denominator 'a)` | 0, 1 | |
  | `(realpart 'a)`, `(imagpart 3)` | 0, 0 | |
  | `(symbol-name 7)`, `(symbol-package-name 7)` | `""`, `""` | |
  | `(coerce "ab" 'string)` | `""` | A string is not a list, so it is read as the empty list. Common Lisp gives `"ab"`. |
  | `(coerce '(1 #\a) 'string)` | a string of `(code-char 0)` and `#\a` | A member that is not a character becomes `(code-char 0)`. |
  | `(coerce 'a 'list)` | `NIL` | |
  | `(intern-in-package-of-symbol "X" 3)` | `NIL` | |
  | `(intern-in-package-of-symbol "abc" 'bm-gc)` | `ACL2::\|abc\|` | No case is changed. |
  | `(pkg-witness 7)`, `(pkg-imports 7)` | `ACL2::ACL2-PKG-WITNESS`, `NIL` | |
  | `(bad-atom<= 'a "s")` | `NIL` | Entry 1.1. |

- **ACL2 Core.** The table of [`spec/language.md`](spec/language.md), section 3, gives the same values; a checker computes them, and a runner too.
- **Check.** The lines `value` of `checks/expected/edge.txt` for the primitives, and the 157 lines `value` and `no-value` of `checks/expected/facts.txt`.

### 4.2 Library functions that inherit a completion

- **The axioms.** ACL2's library functions are defined from the primitives, so outside their guards they inherit the completions.
- **ACL2.** With guard checking `:none` it gives the values of the definitions.
- **Example.** With guard checking `:none`:

  | Call | Value | Why |
  |---|---|---|
  | `(floor 7 0)`, `(ceiling 7 0)`, `(truncate 7 0)`, `(round 7 0)` | 0 | The quotient is `(* 7 (/ 0))`, which is 0. |
  | `(mod 7 0)`, `(rem 7 0)` | 7 | `7 - 0 * 0`. |
  | `(floor #c(1 2) 1)`, `(floor 'a 2)` | 0, 0 | The numerator of a complex number is 0. |
  | `(expt 0 0)`, `(expt 0 -1)` | 1, 0 | The reciprocal of 0 is 0. |
  | `(expt 2 1/2)`, `(expt 2 'a)`, `(expt 'a 2)` | 1, 1, 0 | An exponent that is not an integer counts as 0. |
  | `(nth -1 '(a b))`, `(nth 'x '(a b))` | `A`, `A` | An index that is not a natural number counts as 0. |
  | `(nthcdr -1 '(1 2))` | `(1 2)` | |
  | `(char "abc" 5)`, `(char "abc" -1)` | `NIL`, `#\a` | `char` is `nth` of the list of characters, so it can give `NIL`. |
  | `(subseq "abc" 1 5)` | `"bc"` followed by two `(code-char 0)` | `subseq` pads with `NIL`, which `coerce` turns into `(code-char 0)`. |
  | `(take 3 '(1))`, `(update-nth 3 'x nil)` | `(1 NIL NIL)`, `(NIL NIL NIL X)` | Both pad with `NIL`; the first is inside the guard. |
  | `(length 'abc)`, `(len '(1 2 . 3))` | 0, 2 | |
  | `(abs 'a)`, `(max 'a -1)`, `(min 'a 1)` | `A`, `A`, `A` | `abs` gives its argument unless it is negative, and `'a` is not; `max` and `min` compare by `<`, where `'a` is 0. |
  | `(signum 'a)` | 1 | `'a` is neither 0 by `zerop` nor negative. |
  | `(evenp 1/2)`, `(oddp 1/2)`, `(evenp 'a)` | `NIL`, `T`, `T` | `oddp` is the negation of `evenp`, and `(* 'a 1/2)` is the integer 0. |
  | `(zp 1/2)`, `(zp -3)`, `(zip 1/2)` | `T`, `T`, `T` | |
  | `(= 'a 0)`, `(zerop 'a)` | `NIL`, `NIL` | `=` is `equal`. |
  | `(list (1+ 'a) (<= 'a 0) (>= 'a 0) (= 'a 0))` | `(1 T T NIL)` | `'a` is at most 0 and at least 0, and is not 0. |
  | `(assoc-equal nil '(1 (a . 2)))` | 1 | `(car 1)` is `NIL`. |
  | `(string 7)` | the string of `(code-char 0)` | |
  | `(binary-append 1 2)`, `(binary-append '(1 . 2) '(3))` | 2, `(1 3)` | |
  | `(reverse '(1 2 . 3))`, `(last 7)` | `(2 1)`, 7 | |
  | `(char< 'a #\a)` | `T` | |
  | `(ash 1/2 1)`, `(binary-logand 1/2 3)`, `(integer-length 'a)` | 0, 0, 0 | |
  | `(string-append "a" 'b)` | `"a"` | |
  | `(char-upcase 7)` | none | It calls `char-upcase-non-standard` (entry 1.4), which has no code for a non-character. |

- **ACL2 Core.** The library holds these definitions, and a proof or a runner gives the same values. For `(char-upcase 7)` a runner stops, as ACL2 does.
- **Check.** The lines `value` and `no-value` of `checks/expected/edge.txt` for these functions, and the line `top` labelled 4.2.

## 5. Data

### 5.1 Exactly 256 characters

- **The axioms.** `char-code-linear`, `code-char-type`, `code-char-char-code-is-identity` and `char-code-code-char-is-identity` make the characters correspond one to one with the integers 0 to 255. Which character has which code is fixed by the constants that ACL2 reads (entry 5.3).
- **ACL2.** Its characters are exactly the 256 whose codes are below 256; the Lisp under it has more, but ACL2's reader refuses them (entry 5.5).
- **Example.** ACL2 proves `(implies (characterp c) (< (char-code c) 256))` and `(implies (characterp c) (equal (code-char (char-code c)) c))`. `(code-char 255)` is a character. The text `#\` followed by the character with code 233, which ACL2 writes to a file, reads back as `(code-char 233)`.
- **ACL2 Core.** Has the same 256 characters ([`spec/language.md`](spec/language.md), section 1). Entry 10.2 shows ACL2 making a character outside them in program mode.
- **Check.** Lines 5.1; the line `value` for `(code-char 255)`; the line `read` for the character with code 233.

### 5.2 Numbers in ACL2's reader

- **The axioms.** A number is an object; a text that writes it is no part of the logic.
- **ACL2.** It reads numbers with the reader of Common Lisp, with some additions. Many texts give one number.
- **Example.** Each text is read alone from a file by ACL2's `read-object`.

  | Text | Object |
  |---|---|
  | `1/2`, `2/4` | 1/2 |
  | `-3/6` | -1/2 |
  | `-0`, `+5`, `1.` | 0, 5, 1 |
  | `#c(1 0)`, `#c(1/2 0)`, `#C(1 2)` | 1, 1/2, `#c(1 2)` |
  | `#x10`, `#x-1F`, `#b101`, `#o17`, `#36rZ` | 16, -31, 5, 15, 35 |
  | `#u1_000` | 1000 |
  | `#d1.5`, `#d0.1` | 3/2, 3602879701896397/36028797018963968: the rational value of the nearest double-float |
  | `#f0.1` | 1/10 |
  | `#.*bm-c*` | 7, the value of the constant `*bm-c*` |

- **ACL2 Core.** No counterpart: a checker reads only the formats of [`spec/formats.md`](spec/formats.md), where every number has exactly one text, and ACL2 writes the statements. The exporter writes each number in that one text.
- **Check.** The lines `read` of `checks/expected/edge.txt` for these texts.

### 5.3 Characters and strings in ACL2's reader

- **ACL2.** After `#\` it accepts a single character, or one of the names `Space`, `Newline`, `Tab`, `Page`, `Rubout` and `Return`, in any case. In a string, the backslash escapes only the next character.
- **Example.** `#\a`, `#\A`, `#\Space`, `#\space`, `#\Newline`, `#\Tab`, `#\Page`, `#\Rubout` and `#\Return` read as the characters with codes 97, 65, 32, 32, 10, 9, 12, 127 and 13. `#\Linefeed`, `#\Backspace`, `#\Nul`, `#\Null`, `#\Escape`, `#\U+41` and `#\LATIN_SMALL_LETTER_A_WITH_MACRON` are refused. The text `"a\nb"` reads as the string `"anb"`. A string may hold `(code-char 0)` and `(code-char 233)`. `#{"""abc"""}` reads as `"abc"`.
- **ACL2 Core.** No counterpart, as in entry 5.2: [`spec/formats.md`](spec/formats.md) writes a character as `#\` and two hexadecimal digits.
- **Check.** The lines `read` and `no-read` for these texts.

### 5.4 Symbols in ACL2's reader

- **ACL2.** It reads a symbol in upper case, unless bars or a backslash protect the case; a symbol with no package is in the current package, here `ACL2`; a package that imports a name gives the imported symbol (entry 7.5).
- **Example.** `foo` and `Foo` read as `ACL2::FOO`; `|foo|` as `ACL2::|foo|`; `\foo` as `ACL2::|fOO|`; `||` as the symbol with the empty name; `()` as `NIL`; `acl2::car` and `bm-dup::car` as `COMMON-LISP::CAR`; `common-lisp::bm-new` as a new symbol of `COMMON-LISP`; `:k` and `keyword::k` as `KEYWORD::K`. `'x` reads as `(quote x)`, `#'car` as `(function car)`, and `` `(a ,b) `` as `(cons 'a (cons b 'nil))`.
- **ACL2 Core.** No counterpart: [`spec/formats.md`](spec/formats.md) writes every symbol with its package, and the rule of existence decides which symbols there are ([`spec/language.md`](spec/language.md), section 2).
- **Check.** The lines `read` for these texts.

### 5.5 What ACL2's reader refuses

- **ACL2.** It refuses every object that is not ACL2 data, and some texts that would give data.
- **Example.** Refused: `1.5`, `1e3` and `1.5d0`, which are floating-point numbers, and `#c(1.0 2)`; `1/0`; `bm-no-such-package::x` and `sb-ext::gc`, whose packages ACL2 does not know, the second being a package of the Lisp under ACL2; `#:foo`, a symbol in no package; `#(1 2)`, `#*101` and `#p"x"`, a vector, a bit vector and a file name; and the character names of entry 5.3.
- **ACL2 Core.** No counterpart: the formats have no text for these.
- **Check.** The lines `no-read`.

### 5.6 Reading that depends on the host Lisp

- **ACL2.** `#+` and `#-` test the features of the Lisp under ACL2, so one text reads differently on two hosts.
- **Example.** On SBCL, `#+sbcl 1` reads as 1 and `#-sbcl 1 2` as 2; `#+acl2-loop-only 1` reads as 1. `#|c|# 1` reads as 1.
- **ACL2 Core.** No counterpart. A book that uses `#+` or `#-` states what ACL2 read on the host that exported it.
- **Check.** The lines `read` for these texts.

### 5.7 Bad atoms

- **The axioms.** Nothing says that every object is a cons, a number, a character, a string or a symbol; ACL2's logic allows other objects, which it calls bad atoms, and orders them by `bad-atom<=` (entry 1.1).
- **ACL2.** No reader makes a bad atom, and ACL2 cannot prove that none exists.
- **Example.** ACL2 refuses to prove `(or (consp x) (acl2-numberp x) (characterp x) (stringp x) (symbolp x))`.
- **ACL2 Core.** The same: no text writes a bad atom, and the axioms hold of them ([`spec/language.md`](spec/language.md), section 1).
- **Check.** Lines 5.7.

## 6. Admission: where ACL2's tests are not the logic's

### 6.1 Names

- **The axioms.** A definition needs only a new function symbol.
- **ACL2.** It refuses a function named by a keyword or by a symbol of `COMMON-LISP`, a theorem named by a keyword, `T` or `NIL`, and any name in use (`checks/expected/facts.txt`). It also refuses a name that the Lisp under it defines, which depends on the host, and any event that calls a function it holds untouchable.
- **Example.** `(defun load-acl2 (x) x)` and `(defun exit-lisp (x) x)` are refused: each name "has a function definition in raw Common Lisp". `(defun bm-not-in-the-lisp (x) x)` is accepted. A theorem that calls `big-n` is refused, because ACL2 holds `big-n` untouchable.
- **ACL2 Core.** Follows ACL2's rules for names ([`spec/language.md`](spec/language.md), sections 5 and 6), with two exceptions. Names that the host Lisp defines are not in ACL2's world, so no `reserve` line holds them, and they depend on the host. An untouchable function such as `big-n` is a `constrain` statement of the library, which a statement of a book may call. Whether the library should mark either is undecided (`PLAN.md`). No statement that ACL2 writes can take such a name or call such a function, so only a statement written by hand is affected.
- **Check.** Lines 6.1; the lines `refused` and `accepted` about names of `checks/expected/facts.txt`.

### 6.2 The termination machine and ruler-extenders

- **The axioms.** The definitional principle asks that a measure decrease at each recursive call, under the tests that rule it.
- **ACL2.** Its termination machine decides which tests rule a call, by the ruler-extenders of the definition, and does not measure the executable half of an `mbe`. A definition whose only call of itself is in that half is not recursive: ACL2 asks no measure of it and stores no justification.
- **Example.** ACL2 refuses `bm-r0`, whose recursion is ruled only by a test inside an argument of `cons`, and admits the same body with the ruler-extenders `:all`. It holds `bm-mbe-self`, defined as `(mbe :logic x :exec (bm-mbe-self x))`, and its own `string-append`, which calls itself in the executable half of its `mbe`, as not recursive.
- **ACL2 Core.** Asks for exactly ACL2's measure conjectures, by the walk of [`spec/logic.md`](spec/logic.md), section 6, which records the calls and tests of ACL2's machine for all 523 definitions that call themselves in the world ACL2 starts with. A call in the executable half of an `mbe` does not make a `define` statement have obligations, as it does not make a definition recursive in ACL2.
- **Check.** Lines 6.2; the lines `agrees`, `rulers`, `obligation` and the corresponding lines `refused` of `checks/expected/facts.txt`.

### 6.3 Measures that ACL2 guesses

- **The axioms.** A definition is admitted if some measure decreases.
- **ACL2.** With no `:measure`, it guesses `(acl2-count v)` for one formal `v`, and refuses the definition if that fails, even when another measure succeeds.
- **Example.** For `(defun bm-guess (x y) (if (consp y) (bm-guess x (cdr y)) x))` ACL2 stores the measure `(acl2-count y)`. It refuses `bm-up`, which counts `i` up to `n`, with no measure, and admits it with the measure `(nfix (- n i))`.
- **ACL2 Core.** A `define` statement carries no measure; a proof gives one ([`spec/logic.md`](spec/logic.md), section 6). Both events of `bm-up`, had ACL2 admitted both, would be one statement.
- **Check.** Lines 6.3.

### 6.4 Well-founded relations other than `o<`

- **ACL2.** It admits a definition measured with another relation, once a theorem of the class `:well-founded-relation` embeds the relation in `o<`.
- **ACL2 Core.** Such a definition is an ordinary `define`, and the embedding gives a measure under `o<` ([`spec/logic.md`](spec/logic.md), section 6).
- **Example and check.** The lines `well-founded`, `justification`, `termination` and `obligation` for `bm-w` of `checks/expected/facts.txt`.

### 6.5 The body ACL2 stores

- **The axioms.** The equation of a definition is the one it states.
- **ACL2.** It stores the translated body: macros expanded, `let` turned into a lambda application closed over every free variable, `cond`, `and` and `or` into `if`, a constant replaced by its value, `mbe` and `prog2$` into `return-last`. Its prover uses a second, normalized body, from which `return-last` and the like are gone and tests are simplified.
- **Example.** For `bm-body`, written with `let`, `cond`, `and`, `*bm-c*`, `mbe`, `prog2$` and `cw`, ACL2 stores `((lambda (y x) (if (if y (< '7 '9) 'nil) (return-last 'mbe1-raw y y) (cons x (cons (return-last 'progn (fmt-to-comment-window '"x" ... '0 'nil 'nil) x) 'nil)))) (car x) x)`, where `...` is a constant list, and its normalized body is `((lambda (y x) (if y y (cons x (cons x 'nil)))) (car x) x)`.
- **ACL2 Core.** A statement holds the stored, unnormalized body ([`spec/language.md`](spec/language.md), section 7). `set-body` and rules of the class `:definition` change only the body ACL2's prover uses.
- **Check.** Lines 6.5.

### 6.6 Definitions that join the constraint of an `encapsulate`

- **The axioms.** The constraint of an `encapsulate` is what may be assumed of its constrained functions.
- **ACL2.** A function defined, not locally, inside an `encapsulate` with a signature is usually an ordinary definition. Its equation becomes part of the constraint instead in cases such as these: when a constrained function of the `encapsulate` rules its recursion, or when an exported theorem that mentions a constrained function also mentions it. Such a function keeps its body, and its constraint is that of the `encapsulate`. One function of the world ACL2 starts with is of this kind, `apply$-equivalence`, which `defun-sk` defines in ACL2's source file `boot-strap-pass-2-b.lisp` (entry 6.9).
- **Example.** In an `encapsulate` constraining `bm-k`, `bm-k2`, which recurs under the test `(consp x)` alone, is an ordinary definition with no constraint. `bm-k3`, which recurs under the test `(bm-k x)`, joins the constraint: the constraint of `bm-k` is its own theorem and the equation of `bm-k3`, whose origins ACL2 records as `(theorem bm-k-idempotent)` and `(defun bm-k3)`; the constraint of `bm-k3` is the name `BM-K`; and both are siblings. In an `encapsulate` constraining `bm-q`, `bm-q2` is not recursive, but the exported theorem `(equal (car (bm-q2 x)) (bm-q x))` mentions it, so its equation joins the constraint of `bm-q`.
- **ACL2 Core.** Such a function, which ACL2 marks by holding the name of a function of the signature as its constraint, is a function of the `constrain` statement, and its equation is one of the statement's formulas; it has no `define` statement ([`spec/language.md`](spec/language.md), section 7; [`spec/logic.md`](spec/logic.md), section 7). A proof shows the constraint with witnesses, as for any `constrain`.
- **Check.** Lines 6.6, among them the lines `count` and `stored` for the world ACL2 starts with.

### 6.7 Where the constraint of an `encapsulate` is stored

- **ACL2.** It stores the constraint on one function of the `encapsulate`, in its property `constraint-lst-etc`; each of the others holds that function's name in its place. With the formulas it records the origin of each, such as `(theorem name)` for an exported theorem or `(defun f)` for a definition that joined the constraint.
- **Example.** The constraint of `bm-m1` is `((equal (bm-m1 x) (bm-m2 x)))`, with the origin `(theorem bm-m1-m2)`, and that of `bm-m2` is `BM-M1`. In entry 1.4, `char-upcase-non-standard` holds `ALPHA-CHAR-P-NON-STANDARD`.
- **ACL2 Core.** One `constrain` statement holds all the functions and the formulas, each with a name ([`spec/language.md`](spec/language.md), section 7). The origins are no part of the logic.
- **Check.** Lines 6.7, and the line `stored` of 1.4 for `char-upcase-non-standard`.

### 6.8 `defchoose` with `:strengthen`

- **ACL2.** With `:strengthen t` it stores a stronger axiom, which says also that the chosen value depends only on the set of values that satisfy the formula.
- **ACL2 Core.** The `choose` statement carries a second list of variables for that form ([`spec/logic.md`](spec/logic.md), section 6).
- **Example and check.** The lines `choose` and `choose-axiom` of `checks/expected/facts.txt`.

### 6.9 `defun-sk`

- **The axioms.** `(defun-sk bm-exists (x) (exists y (equal y (cons x x))))` defines `bm-exists` by a function that chooses a witness.
- **ACL2.** It expands to an `encapsulate` whose signature is the witness `bm-exists-witness`. Inside, a local `defchoose` makes the witness. Exported are the definition of `bm-exists`, which is not executable and joins the constraint (entry 6.6), and the theorem `bm-exists-suff`. So ACL2 stores no `defchoose` axiom for the witness; the constraint holds the equation of `bm-exists` and `(implies (equal y (cons x x)) (bm-exists x))`.
- **Example.** The event that introduced `bm-exists-witness` is an `encapsulate` whose `defchoose` is inside `local`, followed by `defun-nx bm-exists` and `defthm bm-exists-suff`; ACL2 stores no `defchoose` axiom for the witness; the constraint of `bm-exists` is the name `BM-EXISTS-WITNESS`; the origins of the two formulas are `(defun bm-exists)` and `(theorem bm-exists-suff)`; the body of `bm-exists` begins with `throw-nonexec-error` (entry 2.3).
- **ACL2 Core.** The event is one `constrain` statement, of the witness and of the function, with the two formulas. Its proof needs witnesses that satisfy them, and in general the only such witness is a choice function. A proof introduces one as ACL2 does, by a `choose` entry, which is admitted as a `choose` statement is, and defines the other function from it with a `define` entry ([`spec/logic.md`](spec/logic.md), section 6, "Entries of the proofs").
- **Check.** Lines 6.9.

### 6.10 Redundant events

- **ACL2.** It accepts an event that repeats one it has and does nothing; it refuses the same name with other content. It refuses a repetition, not local, of one of its own definitions that has Common Lisp code of its own.
- **Example.** A repeated theorem and a repeated definition are accepted (`checks/expected/facts.txt`). `(defun zip (x) (declare (xargs :mode :logic :guard (integerp x))) (if (integerp x) (= x 0) t))` is refused.
- **ACL2 Core.** A line that repeats an earlier one byte for byte adds nothing ([`spec/logic.md`](spec/logic.md), section 6). ACL2's refusal leaves no event, so no statement differs.
- **Check.** The line `refused` labelled 6.10; the lines about repeated events of `checks/expected/facts.txt`.

### 6.11 `local`

- **ACL2.** A local event is gone from a book as other books see it. It refuses a local `defaxiom` and a `defaxiom` inside `encapsulate`.
- **ACL2 Core.** A local event becomes no statement; a proof may hold the lemmas and definitions it gave ([`spec/language.md`](spec/language.md), section 7).
- **Example and check.** The lines `refused` and `accepted` about axioms of `checks/expected/facts.txt`.

### 6.12 Tests that leave nothing in a statement

- **ACL2.** It refuses events for reasons that are not logical: a formal that is not used, or that only passes itself to a recursive call, unless declared; a theorem whose form cannot be a rule of the class asked for.
- **Example.** It refuses `bm-irr`, whose formal `y` is irrelevant, and accepts it with `(declare (irrelevant y))`. It refuses `(defthm bm-same (equal (bm-k x) (bm-k x)))` as a rewrite rule that rewrites a term to itself, and accepts it with `:rule-classes nil`. `checks/expected/facts.txt` records the same for an unused formal.
- **ACL2 Core.** Both events of each pair are one statement, which a checker admits. A declaration and a rule class are no part of a statement, so ACL2 Core cannot tell the two events apart and cannot follow. ACL2's refusal leaves no event, so no statement that ACL2 writes is affected.
- **Check.** Lines 6.12.

### 6.13 Single-threaded objects in the logic

- **ACL2.** `defstobj` defines the functions of a single-threaded object on lists, and `defabsstobj` defines each exported function as a call of its logical function.
- **Example.** The body of `update-bm-arri` is `(update-nth-array '0 i v bm-st)`.
- **ACL2 Core.** One `define` statement for each such function ([`spec/language.md`](spec/language.md), section 7). Entry 2.7 is what they do at run time.
- **Check.** The line `stored` labelled 2.7.

### 6.14 `loop$` and lambda objects

- **The axioms.** A quoted lambda is a constant.
- **ACL2.** It measures the recursive calls inside the quoted lambda of a `loop$` in a definition declared with `:loop$-recursion t`. It refuses a quoted lambda with a free variable.
- **Example.** ACL2's termination theorem for `bm-l1` asks that `(acl2-count nv0)` be below `(acl2-count x)` for every member `nv0` of `x`, and it refuses `bm-l2`, whose recursion does not end (`checks/expected/facts.txt`). It refuses `(defun bm-free-lambda (x) (apply$ '(lambda (x) (cons x y)) (list x)))`.
- **ACL2 Core.** Treats the quoted lambda as a constant, so such a definition has no obligation beyond `(o-p m)`; its equation is still one that a function satisfies. Following ACL2 is undecided (`PLAN.md`). The refusal of a lambda with a free variable is a test of the kind of entry 6.12.
- **Check.** The line `refused` labelled 6.14; the lines `termination` and `obligation` for `bm-l1` of `checks/expected/facts.txt`.

## 7. Packages

### 7.1 The packages ACL2 starts with

- **The axioms.** Four `defaxiom` events give the imports of `ACL2`, `KEYWORD`, `ACL2-INPUT-CHANNEL` and `ACL2-OUTPUT-CHANNEL`. `ACL2-USER`, `ACL2-PC` and `BIB` are declared by `defpkg`, which stores an axiom for each. `COMMON-LISP` has none (entry 1.2).
- **ACL2.** It starts with these eight packages. It accepts a `defpkg` of one of them with its own imports as redundant, and it holds no rule named `COMMON-LISP-PACKAGE`.
- **Example.** ACL2 holds an axiom named `ACL2-USER-PACKAGE`. The list of packages, and the imports of each, are lines of `checks/expected/facts.txt`. It accepts `(defpkg "KEYWORD" nil)` and `(defpkg "COMMON-LISP" nil)`, each as redundant, and `(defthm common-lisp-package t :rule-classes nil)`.
- **ACL2 Core.** The ground theory holds the first five; the library holds the other three as `package` statements ([`spec/logic.md`](spec/logic.md), sections 3 and 7). Only the four packages with an axiom give a fact, so `ACL2::COMMON-LISP-PACKAGE` is not in use, as in ACL2. A `package` statement of a package of the ground theory is refused, even one that is, byte for byte, a line of the ground theory, since the ground theory is no input and a package may not be declared twice; ACL2 accepts such a `defpkg` as redundant. Following ACL2 is undecided (`PLAN.md`). No statement that ACL2 writes is affected.
- **Check.** Lines 7.1; the lines `packages`, `package` and `imports` of `checks/expected/facts.txt`.

### 7.2 The names of packages

- **The axioms.** A package name is a string; the axioms ask nothing more of it.
- **ACL2.** It refuses the empty name, a name with a lower-case letter, `"LISP"`, a name that begins with `ACL2_*1*_`, a name whose rule `NAME-PACKAGE` would take a name in use, and the name of a package of the Lisp under it. Whether a character with a code from 128 to 255 is lower case is decided by the host.
- **Example.** Refused: `""` and `"Bm-p3"` (`checks/expected/facts.txt`); `"LISP"`; `"ACL2_*1*_BM"`; `"IN"`, whose rule would be `IN-PACKAGE`, a macro; `"SB-EXT"` and `"CL-USER"`, packages of SBCL; `"BM"` followed by `(code-char 233)`. Accepted: `"BM-A::B"`, `"BM A"`, `"ACL2-PKG-BM"`, and `"BM"` followed by `(code-char 201)`.
- **ACL2 Core.** Asks the same of a `package` statement, except for the names of host packages and for the case of characters 128 to 255 ([`spec/logic.md`](spec/logic.md), section 6). Those depend on the host; the second can be followed with the tables of entry 1.4, which is undecided (`PLAN.md`).
- **Check.** The lines labelled 7.2; the lines `refused` about packages of `checks/expected/facts.txt`.

### 7.3 Imports are sorted and have no repeats

- **The axioms.** The axiom a `defpkg` adds is `(equal (pkg-imports "NAME") 'imports)`.
- **ACL2.** It sorts the imports by name and drops a symbol that is repeated; the axiom holds the sorted list. It refuses two different symbols with one name.
- **Example.** Declared with `(car car)`, `BM-DUP` imports `(COMMON-LISP::CAR)`, and ACL2 stores the axiom `(equal (pkg-imports '"BM-DUP") '(car))`. Declared with `(zebra :apple car)`, `BM-ORDER` imports `(KEYWORD::APPLE COMMON-LISP::CAR ACL2::ZEBRA)`.
- **ACL2 Core.** A `package` statement must give its imports in ACL2's order, and `pkg-imports` gives them in that order ([`spec/logic.md`](spec/logic.md), section 6).
- **Check.** Lines 7.3; the line `package` for `BM-P4` of `checks/expected/facts.txt`.

### 7.4 `defpkg` only at the top level

- **ACL2.** `defpkg` is not one of its embedded events: it may not stand inside `encapsulate` or `progn`, nor be the expansion of `make-event`.
- **Example.** A `defpkg` inside `encapsulate`, one inside `progn`, and one made by `make-event` are refused.
- **ACL2 Core.** A `package` statement is a line of the statements, before the lines that use it ([`spec/logic.md`](spec/logic.md), section 6).
- **Check.** Lines 7.4.

### 7.5 A symbol written with one package that belongs to another

- **The axioms.** `symbol-package-name-intern-in-package-of-symbol` and the imports of a package make an imported name denote the imported symbol.
- **ACL2.** `acl2::car` is `COMMON-LISP::CAR`, whose package name is `"COMMON-LISP"`.
- **Example.** `acl2::car` and `bm-dup::car` read as `COMMON-LISP::CAR` (entry 5.4); `(symbol-package-name 'bm-p4::zebra)` is `"ACL2"` (`checks/expected/facts.txt`).
- **ACL2 Core.** Every symbol is written with its own package, and the rule of existence refuses a text such as `ACL2::CAR` ([`spec/language.md`](spec/language.md), section 2).
- **Check.** The lines `read` of 5.4; the lines `value` for `symbol-package-name` and `intern-in-package-of-symbol` of `checks/expected/facts.txt`.

### 7.6 Hidden packages

- **The axioms.** None about a hidden package.
- **ACL2.** It keeps the package, refuses `pkg-imports` and `pkg-witness` on its name (entry 2.8) and `symbol-package-name` on its symbols (2.9), computes `intern-in-package-of-symbol` at them (1.3), and accepts a later open declaration with the same imports.
- **Example.** `BM-HIDDEN` is hidden; ACL2 cannot prove what it imports (`checks/expected/facts.txt`).
- **ACL2 Core.** The `hidden-package` statement does each of these ([`spec/logic.md`](spec/logic.md), section 6; [`spec/language.md`](spec/language.md), section 4).
- **Check.** Lines 1.3 and 2.9; the lines `hidden-package`, `no-plain` and the corresponding `refused` and `accepted` of `checks/expected/facts.txt`.

## 8. Ways a session leaves the axioms

### 8.1 `defaxiom`

- **ACL2.** It adds the formula with no proof, and allows `defaxiom` only at the top level of a book. The certificate of a book has a mark `:axiomsp` (entry 8.3).
- **ACL2 Core.** An `axiom` statement, which the verdict counts ([`spec/logic.md`](spec/logic.md), section 6).
- **Example and check.** The lines `refused` and `accepted` about axioms of `checks/expected/facts.txt`.

### 8.2 `skip-proofs`

- **ACL2.** It admits the event inside without its proofs, and records that it did.
- **Example.** `(skip-proofs (defthm bm-one-is-two (equal 1 2)))` is accepted. A definition of `bm-bad` whose recursion does not end is refused, and accepted under `skip-proofs`; after it ACL2 proves `NIL`. ACL2 records nothing of skipped proofs before such an event, and the event after it.
- **ACL2 Core.** The event inside becomes its statement, which still needs its proof, or is skipped and counted ([`spec/language.md`](spec/language.md), section 7).
- **Check.** Lines 8.2.

### 8.3 Books with no certificate

- **ACL2.** It includes a book with no certificate, admitting its theorems without proof, and records no certificate for it.
- **Example.** Including `build/edge-false`, which states `(equal 1 2)`, is accepted, and ACL2 then proves `NIL`. The marks of the certified book `build/edge-hidden` are `((:skipped-proofsp) (:axiomsp) (:ttags))`; those of `build/edge-false` are `NIL`.
- **ACL2 Core.** The statements of the book still need their proofs.
- **Check.** Lines 8.3.

### 8.4 Trust tags, `progn!` and raw Lisp

- **ACL2.** With a trust tag in force, `progn!` may change the Lisp under ACL2: it may redefine the Common Lisp code of a function, which ACL2 then runs and proves theorems by. `sys-call`, `progn!` and `defattach` with `:skip-checks t` are refused without a trust tag. ACL2 records each trust tag.
- **Example.** With `bm-two` defined to give 2, `(progn! (set-raw-mode t) (defun bm-two () 5))` under the tag `:bm-edge` makes `(bm-two)` give 5; ACL2 proves `(equal (bm-two) 5)` and then `NIL` from that theorem and the definition. `(sys-call "true" nil)` then gives `NIL`. ACL2 records no trust tag before `(defttag :bm-edge)` and `((:bm-edge nil))` after it.
- **ACL2 Core.** A statement is taken from ACL2's world and still needs its proof, and a checker never runs code. A world changed under a trust tag may hold what the book's text does not say; whether the exporter refuses such a world or marks it is undecided (`PLAN.md`).
- **Check.** Lines 8.4.

### 8.5 Redefinition

- **ACL2.** After `(redef!)` it accepts a new definition of a function and keeps the theorems proved about the old one, and records the redefinition.
- **Example.** With `bm-one` defined to give 1 and the theorem `(equal (bm-one) 1)`, a new definition giving 3 is accepted; `(bm-one)` gives 3, and ACL2 proves `NIL` from the old theorem.
- **ACL2 Core.** The world holds one definition, the new one; the old theorem is a statement that needs a proof and has none.
- **Check.** Lines 8.5.

### 8.6 `make-event`

- **ACL2.** A program computes the event, with access to `state`; ACL2 stores the event it computed.
- **Example.** A `make-event` that counts the packages ACL2 knows stores `(defun bm-made nil '28)`.
- **ACL2 Core.** The computed event becomes the statement ([`spec/language.md`](spec/language.md), section 7). `make-event` leaves the axioms only through what the computed event does.
- **Check.** Lines 8.6.

## 9. Where the logic is not a set of axioms

### 9.1 Induction up to ε<sub>0</sub>

- **The axioms.** Induction is a principle: it rests on the fact, outside the logic, that `o<` is well founded on the ordinals that `o-p` recognizes.
- **Example.** ACL2 refuses to prove `(equal (len (append x y)) (+ (len x) (len y)))` without induction, and proves it with induction.
- **ACL2 Core.** The rule `induct` ([`spec/logic.md`](spec/logic.md), section 5).
- **Check.** Lines 9.1.

### 9.2 The definitional principle

- **The axioms.** A definition is admitted only when its recursion is shown to end; an equation that some function satisfies is not enough.
- **Example.** ACL2 refuses `(defun bm-zero (x) (if (zp x) 0 (bm-zero (+ x 1))))`, which the function that is always 0 satisfies.
- **ACL2 Core.** The same: the obligations of termination cannot be proved ([`spec/logic.md`](spec/logic.md), section 6).
- **Check.** Lines 9.2.

### 9.3 Functional instantiation

- **ACL2.** It proves a theorem about one function from a theorem about a constrained function, after proving the constraint of the second for the first.
- **Example.** ACL2 proves that `bm-hh` applied twice is `bm-hh` applied once, for atoms, from the theorem `bm-h-twice` about the constrained `bm-h`.
- **ACL2 Core.** Has no such rule; a proof repeats the steps of the general theorem for the instance. [`PLAN.md`](PLAN.md), step 8, lists the rule among the larger steps.
- **Check.** Lines 9.3.

### 9.4 Choice

- **ACL2.** `defchoose` adds an axiom that the axiom of choice, outside the logic, justifies.
- **ACL2 Core.** The `choose` statement ([`spec/logic.md`](spec/logic.md), section 6).
- **Example and check.** The lines `choose` of `checks/expected/facts.txt`.

### 9.5 Proof by evaluation

- **ACL2.** Its prover replaces a call on constants by the value its evaluator gives, and the evaluator may run a function's Common Lisp code: entry 8.4 shows the prover using code that differs from the definition. So a theorem proved by evaluation rests on that code.
- **ACL2 Core.** A checker computes only the primitives, by the table of [`spec/language.md`](spec/language.md), section 3; every other evaluation is a proof by the rules. It follows ACL2 except in entries 1.4, 1.5 and 8.4, where ACL2's evaluation goes beyond what the definitions and constraints give.
- **Check.** The lines of those entries.

### 9.6 The built-in clauses about `acl2-count`

- **The axioms.** None of the 84 says that the conses are well founded, and neither does the equation of `acl2-count`. The axioms and the equations of the ground theory are all true of a universe with an endless chain of conses, each the `cdr` of the one before, on which `acl2-count` is negative. So they do not give that `acl2-count` is an ordinal, nor that it is smaller on the `cdr` of a cons.
- **ACL2.** Its prover starts with 23 built-in clauses that say so: `(o-p (acl2-count x))`, and that `car`, `cdr`, one less than a positive integer, `realpart` and `imagpart` have a smaller `acl2-count`, each under the tests ACL2 recognizes. They are the constant `*initial-built-in-clauses*` of its source file `simplify.lisp`. ACL2 takes them as true with no proof: each carries the same rule name, which names no rule, and ACL2 admits `acl2-count` itself with its proof of termination skipped. A measure conjecture that an instance of one of them subsumes counts as proved.
- **Example.** ACL2 proves `(o-p (acl2-count x))` and `(implies (consp x) (o< (acl2-count (cdr x)) (acl2-count x)))`, and it admits `(defun bm-cdrs (x) (if (consp x) (bm-cdrs (cdr x)) x))` with no measure given. The rule name it holds for all 23 clauses is `(:fake-rune-for-anonymous-enabled-rule nil)`, and the event by which it admits `acl2-count` is `(verify-termination-boot-strap :skip-proofs acl2-count (declare (xargs :mode :logic)))`.
- **ACL2 Core.** The ground theory holds the 23 clauses as facts, `"built-in-clause-1"` to `"built-in-clause-23"`, in ACL2's words and ACL2's order ([`spec/logic.md`](spec/logic.md), section 3). They are assumptions of ACL2's, which ACL2 Core shares: together they say that the conses are well founded. A proof of termination cites them as it cites an axiom. [`spec/logic.md`](spec/logic.md), sections 1 and 10, names this among the things that stand beside ACL2's axioms.
- **Check.** Lines 9.6; `checks/ground.lsp`, which takes the clauses from ACL2's constant as it runs and has ACL2 prove each.

## 10. Program mode

### 10.1 `mbe` in program mode

- **The axioms.** A function in program mode has no axiom.
- **ACL2.** It runs a function in program mode as Common Lisp code, so an `mbe` in it runs its executable half, under every setting of guard checking. The two halves need not agree.
- **Example.** `bm-pm` is `(mbe :logic (list 'logic x) :exec (list 'exec x))` in program mode: `(bm-pm 1)` gives `(exec 1)` under `:none` and under `t`.
- **ACL2 Core.** The program text of a function in program mode holds the body ACL2 runs, with each `mbe` replaced by its executable half ([`spec/language.md`](spec/language.md), section 7).
- **Check.** Lines 10.1.

### 10.2 Primitives outside their guards in program mode

- **ACL2.** Under guard checking `t`, a function in program mode whose own guard holds runs its Common Lisp code, where a primitive outside its guard does what Common Lisp does. Under `:none` it gives the completions.
- **Example.** Each function below is in program mode and calls one primitive. Under `t`: `eq` on two strings `"a"` made apart gives `NIL`, where the logic gives `T`; `(code-char 300)` gives a character with code 300, which is not an ACL2 character, so that `(< (char-code (bm-pcc 300)) 256)` is `NIL`; `(coerce "ab" 'string)` gives `"ab"`, where the completion gives `""`; and `(car 7)` gives no value. Under `:none` the first three give `T`, 0 and `""`.
- **ACL2 Core.** A runner gives the completions, as ACL2 does under `:none` (entry 2.4). The values under `t` depend on the host and Common Lisp leaves them undefined, so they cannot be followed.
- **Check.** Lines 10.2.

### 10.3 Functions in program mode with Common Lisp code only

- **ACL2.** It lists 106 of the functions in program mode it starts with as having Common Lisp code that differs from their definitions, to be run only as that code.
- **ACL2 Core.** No program text exists for them, and a runner refuses a call of them ([`spec/language.md`](spec/language.md), section 7). This cannot be followed without that code.
- **Example and check.** The line `count` "of those, functions that ACL2 lists as having raw code" of `checks/expected/facts.txt`.
