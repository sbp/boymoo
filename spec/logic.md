# The logic

This document defines what a checker checks: the facts it starts from, the eight rules by which a proof derives new facts, the conditions under which each statement is admitted, and what a verdict means. [`language.md`](language.md) defines data, terms and statements, and [`formats.md`](formats.md) the text of the inputs and of the verdict.

The logic is ACL2's. Nothing here is new mathematics: each axiom is ACL2's, each rule is one that ACL2's logic allows, and each way of admitting a statement is one of ACL2's principles of extension. What is new is that every proof is written out in steps so small that a short program can check them, and that the checker takes nothing from ACL2 but the statements.

Statements about ACL2 are confirmed against ACL2 8.7 by `sh checks/run.sh`, run from the root of the repository. It was last run on 2026-11-26 and printed `all checks passed`. The files `language.md`, `logic.md`, `formats.md` and `ground.txt` are in the directory `spec/`; every other path is given from the root of the repository.

## 1. What a verdict means

**If a checker says `accepted`, then every theorem of the library and of the statements follows, by the rules of ACL2's logic, from ACL2's axioms about its primitive functions, the imports of the packages that the library and the statements declare, and the definitions, constraints and choice axioms among them; and the packages can all be as declared, and each of the other additions is met by functions that exist, so that none of them makes a false statement about what stood before it provable.**

Four things stand beside ACL2's axioms in this, because ACL2 itself reasons with them although it states none as an axiom: that the package `COMMON-LISP` imports nothing, that `bad-atom<=` gives `NIL` on data, that a hidden package imports what its statement declares, and the built-in clauses of its prover about `acl2-count`, which say that the conses are well founded (sections 3 and 10).

If it says `provisional`, the same holds with these added as assumptions, each of which the verdict counts: the formula of every `axiom` statement, the facts of every statement or `define` entry whose entry is `skip`, and the facts of every statement of the library that is given.

Section 9 lays out the argument in seven steps. It holds whoever wrote the four inputs. That the statements say what a book says is not a claim of the checker: ACL2 writes them, and `PLAN.md` says how that is cross-checked.

## 2. Formulas and clauses

A term used as a **formula** claims that its value is not `NIL`, whatever the values of its variables. This is ACL2's convention.

A **clause** is a list of terms, its **literals**. A clause claims that, whatever the values of its variables, at least one of its literals has a value other than `NIL`. The clause with no literals claims something false. The clause with the one literal `F` claims what the formula `F` claims, and it is called the clause of `F`.

A **fact** is a clause that the checker holds as established, under a name. The name of a fact is a symbol or a string. Strings name only facts of the ground theory, so no statement and no lemma can take such a name.

## 3. The ground theory

The ground theory is what every checker holds before it reads anything. It is the file [`ground.txt`](ground.txt), 219 lines in the format of `formats.md`, and it is part of this specification: a checker has its contents built in. It is no input: a checker takes it as it stands, applies to it none of the conditions of section 6, and owes no verdict on a text of the ground theory other than this one. Every line of it is written by ACL2 itself. The check `checks/ground.lsp` writes the file again from ACL2's world, and `checks/run.sh` compares the two byte for byte.

| Lines | Count | What they are |
|---|---|---|
| `package` | 5 | The packages `COMMON-LISP`, `ACL2-INPUT-CHANNEL`, `ACL2-OUTPUT-CHANNEL`, `ACL2` and `KEYWORD`, with their imports. `ACL2` imports 978 symbols of `COMMON-LISP`; the others import nothing. |
| `specials` | 1 | The 122 symbols of `COMMON-LISP` that ACL2 refuses as variables: its constant `*common-lisp-specials-and-constants*` (`language.md`, section 5). |
| `primitive` | 32 | The primitive functions and the number of arguments of each (`language.md`, section 3). |
| `define` | 37 | ACL2's definitions of the functions that the facts below and the principles of this document mention. |
| `clause` with a string name that does not begin `built-in-clause-` | 41 | Facts that ACL2 has no axiom for, because they are part of its prover. ACL2 proves each in the check. |
| `clause` named `"built-in-clause-1"` to `"built-in-clause-23"` | 23 | ACL2's built-in clauses about `acl2-count`, which its prover takes as true with no proof. |
| `clause` with a symbol name | 80 | ACL2's axioms, each under ACL2's own name. |

### The packages

ACL2 has 84 axioms: the `defaxiom` events of its source file `axioms.lisp`. Four of them have the form `(equal (pkg-imports "NAME") '(imports))`, which is exactly what a `package` statement says (section 6): `acl2-package`, `keyword-package`, `acl2-input-channel-package` and `acl2-output-channel-package`. The ground theory holds those four as its `package` lines, and their facts have ACL2's names for them. The fifth `package` line says that `COMMON-LISP` imports nothing. ACL2 has no axiom that says so, but its evaluator computes with it, and ACL2 proves `(equal (pkg-imports "COMMON-LISP") nil)` by evaluation (section 10). Each `package` line lists the imports in the order in which ACL2 holds them, which for `ACL2` is not the order of their names, so these lines need not meet condition 5 of a `package` statement. Only the four packages for which ACL2 has an axiom give a fact and bring the name of their rule into use (section 4); `COMMON-LISP` gives neither, so `ACL2::COMMON-LISP-PACKAGE` is not in use, and ACL2, which holds no rule of that name, admits a theorem named so (`EDGE-CASES.md`, entry 7.1).

### The definitions

The ground theory defines 37 functions. In the order of the file they are: `eq`, `booleanp`, `implies`, `not`, `true-listp`, `integer-abs`, `len`, `length`, `acl2-count`, `eql`, `atom`, `endp`, `null`, `symbol-listp`, `return-last`, `=`, `zp`, `fix`, `natp`, `posp`, `o-finp`, `o-first-expt`, `o-first-coeff`, `o-rst`, `o<`, `character-listp`, `member-symbol-name`, `member-eq-exec$guard-check`, `member-eq-exec`, `member-equal`, `no-duplicatesp-eq-exec$guard-check`, `no-duplicatesp-eq-exec`, `no-duplicatesp-equal`, `make-character-list`, `bad-atom`, `o-p`, `mv-nth`.

They are the functions that ACL2's axioms, its built-in clauses and the facts below mention; `not`, which the rule `cut` reads; `o-p` and `o<`, the ordinals and their order, which induction and termination are stated with; `acl2-count`, ACL2's measure of the size of an object; `true-listp` and `mv-nth`, which the axiom of a `choose` statement may mention; and every function that the definitions of those call. Each line gives ACL2's own formals and the body ACL2 stores for the definition, and the ruler-extenders ACL2 stores for it, or `NIL` where the function does not call itself.

The equation of each is a fact, under the function's name. These equations are taken as axioms, as ACL2 takes them. ACL2 admits `o<`, `len`, `length` and `acl2-count` with their proofs of termination skipped (`verify-termination-boot-strap :skip-proofs` in `axioms.lisp`). Termination is stated with `o<`, and the measure ACL2 stores for `acl2-count` is `(acl2-count x)` itself. A checker asks nothing more of the ground definitions, and they are not counted in a verdict.

**Why `acl2-count` is given, and why its equation is not enough.** To show that a recursion on the `car` or the `cdr` of a cons ends, a proof needs a measure that is smaller on the parts of a cons than on the cons. A term that looks only to a fixed depth into its argument is no such measure, because two long lists, one the `cdr` of the other, look the same to it. So the first such measure is a function defined by that very recursion, and its own termination cannot be shown before it exists. `acl2-count` is that function for ACL2.

The equation of `acl2-count` does not make it a measure. Nothing in ACL2's axioms or in the equations of the ground theory says that the conses are well founded. They are all true of a universe that holds, besides the data, an endless chain of conses, each the `cdr` of the one before and each with the `car` 0, on which `acl2-count` falls by one at each step for ever and so is negative from some point on. There `(o-p (acl2-count x))` is false, and so nothing shows that `(o< (acl2-count (cdr x)) (acl2-count x))` holds of a cons. That `acl2-count` gives an ordinal, and that it is smaller on the parts of a cons, are further facts. ACL2 does not prove them: its prover has them built in, and the ground theory takes them as ACL2 has them (below, "ACL2's built-in clauses"). With the equation and those clauses, the termination of every other definition can be proved and need not be assumed.

### The meaning of `if` and `equal`

ACL2 states the meaning of `if` and `equal` in a comment of `axioms.lisp`, under the heading "IF and EQUAL", as four axioms that are "not expressed in the ACL2 language", together with the convention of section 2. These are those four, and the convention, as clauses.

| Name | Clause | What it says |
|---|---|---|
| `"if-nil"` | `((equal (if 'nil y z) z))` | `if` on `NIL` gives its third argument. |
| `"if-non-nil"` | `((equal x 'nil) (equal (if x y z) y))` | `if` on anything else gives its second. |
| `"equal-same"` | `((equal (equal x x) 't))` | `equal` gives `T` on one object. |
| `"equal-different"` | `((equal x y) (equal (equal x y) 'nil))` | `equal` gives `NIL` on two objects. |
| `"non-nil-true"` | `((equal x 'nil) x)` | The convention: a term whose value is not `NIL` holds as a literal. |

### Facts that ACL2 builds into its prover

ACL2 states the following 36 in no axiom. They are in the code with which it computes the type of a term: the constants and tables of its source files `type-set-a.lisp` and `type-set-b.lisp`, whose function `type-set-primitive` treats each primitive. ACL2 proves each of the 36 in the check. The comment of `axioms.lisp` before the theorem `basic-tau-rules` says of the disjointness of the kinds that "these facts are all built into type-set". Here each is written as ACL2 would print it; the exact term is in `ground.txt`.

| Names | What they say |
|---|---|
| `"booleanp-consp"`, `"booleanp-integerp"`, `"booleanp-rationalp"`, `"booleanp-complex-rationalp"`, `"booleanp-acl2-numberp"`, `"booleanp-stringp"`, `"booleanp-symbolp"`, `"booleanp-<"` | Each recognizer, and `<`, gives `T` or `NIL`: `(booleanp (consp x))` and so on. |
| `"consp-not-acl2-numberp"`, `"consp-not-characterp"`, `"consp-not-stringp"`, `"consp-not-symbolp"`, `"acl2-numberp-not-characterp"`, `"acl2-numberp-not-stringp"`, `"acl2-numberp-not-symbolp"`, `"characterp-not-stringp"`, `"characterp-not-symbolp"`, `"stringp-not-symbolp"` | No object is of two of the five kinds: `(implies (consp x) (not (acl2-numberp x)))` and so on. |
| `"rationalp-acl2-numberp"`, `"complex-rationalp-acl2-numberp"`, `"acl2-numberp-cases"`, `"complex-rationalp-not-rationalp"`, `"imagpart-rationalp"` | The numbers are the rationals and the complex rationals, which are disjoint, and the imaginary part of a rational is 0. |
| `"integerp-binary-+"`, `"integerp-binary-*"`, `"integerp-unary--"`, `"rationalp-binary-+"`, `"rationalp-binary-*"`, `"rationalp-unary--"`, `"rationalp-unary-/"` | Sums, products and negatives of integers are integers; sums, products, negatives and reciprocals of rationals are rational. |
| `"integer-discrete"` | No integer lies between 0 and 1: `(implies (and (integerp x) (< 0 x)) (not (< x 1)))`. |
| `"consp-cons"`, `"stringp-symbol-name"`, `"integerp-char-code"`, `"char-code-non-negative"`, `"stringp-coerce"` | `cons` gives a cons; `symbol-name` gives a string; `char-code` gives an integer that is not negative; `coerce` gives a string unless its second argument is `LIST`. |

This list is not claimed to be complete. If ACL2 proves something about the primitives that does not follow from the ground theory, the remedy is to add the missing fact here and to `checks/ground.lsp`, where ACL2 must prove it. Such an addition cannot make the logic unsound, because each fact added is a theorem of ACL2.

### ACL2's built-in clauses

ACL2's prover holds a list of clauses that it takes as true, its **built-in clauses**. The standard ACL2 8.7 starts with 23 of them, all about `acl2-count`: the value of the constant `*initial-built-in-clauses*` of its source file `simplify.lisp`, from which ACL2 sets the list in its world when it builds itself. ACL2 uses them through its function `built-in-clausep`: a clause that an instance of a built-in clause subsumes counts as proved. It makes that test on the measure conjectures and the guard conjectures of a definition before it tries to prove them, and as the first step of its prover on any clause. This is how ACL2 admits a recursion on the `car` or the `cdr` of a cons, or one that counts a positive integer down, measured by `acl2-count`, with nothing left to prove.

**ACL2 assumes these clauses and does not prove them.** Where a proved rule has its name, each of the 23 has a mark that names no rule, the same for all, which ACL2's source calls a fake rune: the clauses are a constant of the source, set into ACL2's world as they stand, and no proof stands behind one. ACL2 admits `acl2-count` itself with its proof of termination skipped, by the event `(verify-termination-boot-strap :skip-proofs acl2-count ...)`. In the check ACL2 proves each of the 23, as it proves the 41 other facts for which it has no axiom. That shows that ACL2 holds each as true and no more than that: its prover starts from these clauses, and from a type for `acl2-count`, a natural number, that it worked out from the definition it admitted without proof.

**What they amount to.** Together with the equation of `acl2-count`, the first clause says that `acl2-count` gives a natural number on every object. A function to the natural numbers that is one more than the sum of its values on the `car` and the `cdr` of a cons exists only if no chain of conses goes on for ever, each the `car` or the `cdr` of the one before. So these clauses say that **the conses are well founded**: every object is built from atoms in finitely many steps. That is true of the data, and it is an assumption of ACL2's logic that none of its axioms states. The ground theory holds all 23 as ACL2 states them: ACL2 Core uses what ACL2 uses, and a proof of termination can then cite the clause that ACL2's prover would have found.

**Their names and their form.** ACL2 gives the clauses no names. Here the clause at place N of ACL2's constant, counting from 1, is named `"built-in-clause-N"`. The check takes them from the constant as it runs, so each line is written by ACL2, with the literals in ACL2's order: the conclusion first, then the tests, each as the literal that is false when the test holds. A version of ACL2 with other clauses would show in the check. Here each is written as ACL2 would print it; the exact terms are in `ground.txt`.

| Name | Clause | What it says |
|---|---|---|
| `"built-in-clause-1"` | `((o-p (acl2-count x)))` | `acl2-count` gives an ordinal. |
| `"built-in-clause-2"`, `"built-in-clause-3"` | `((o< (acl2-count (car x)) (acl2-count x)) (not (consp x)))`, and the same with `cdr` | The `car` and the `cdr` of a cons are smaller. |
| `"built-in-clause-4"`, `"built-in-clause-5"` | `((o< (acl2-count (car x)) (acl2-count x)) (atom x))`, and the same with `cdr` | The same, for an object that is not an `atom`. |
| `"built-in-clause-6"`, `"built-in-clause-7"` | `((o< (acl2-count (car x)) (acl2-count x)) (endp x))`, and the same with `cdr` | The same, for an object that is not `endp`. |
| `"built-in-clause-8"`, `"built-in-clause-9"` | `((o< (acl2-count (binary-+ x '-1)) (acl2-count x)) (zp x))`, and the same with `(binary-+ '-1 x)` | One less than `x` is smaller, when `x` is not `zp`. |
| `"built-in-clause-10"`, `"built-in-clause-11"`, `"built-in-clause-12"`, `"built-in-clause-13"` | `((o< (acl2-count (binary-+ x '-1)) (acl2-count x)) (not (integerp x)) L ...)`, where the last literals are `(not (< '0 x))`; or `(< x '0)` with `(= x '0)`; or `(< x '0)` with `(= '0 x)`; or `(< x '0)` with `(equal x '0)` | The same, when `x` is an integer above 0, or an integer that is not below 0 and is not 0, the last written in three ways. |
| `"built-in-clause-14"`, `"built-in-clause-15"`, `"built-in-clause-16"`, `"built-in-clause-17"` | The same four with `(binary-+ '-1 x)` | The same. |
| `"built-in-clause-18"`, `"built-in-clause-19"` | `((o< (acl2-count (realpart x)) (acl2-count x)) (not (complex-rationalp x)))`, and the same with `imagpart` | The real and the imaginary part of a complex rational are smaller. |
| `"built-in-clause-20"`, `"built-in-clause-21"`, `"built-in-clause-22"`, `"built-in-clause-23"` | `((o< (acl2-count (cdr x)) (acl2-count x)) (not (true-listp x)) L)`, where `L` is `(eq x 'nil)`, `(null x)`, `(eq 'nil x)` or `(equal x 'nil)` | The `cdr` of a true list that is not `NIL` is smaller. |

A book can give ACL2 more built-in clauses, as theorems of the rule class `:built-in-clause`. Those are proved, and each is a `theorem` statement like any other.

### ACL2's axioms

The other 80 of ACL2's 84 axioms are facts under ACL2's names. The clause of each has one literal, the formula ACL2 stores for the axiom.

| Group | Names |
|---|---|
| Conses (4) | `car-cdr-elim`, `car-cons`, `cdr-cons`, `cons-equal` |
| Numbers (28) | `nonnegative-product`, `closure`, `associativity-of-+`, `commutativity-of-+`, `unicity-of-0`, `inverse-of-+`, `associativity-of-*`, `commutativity-of-*`, `unicity-of-1`, `inverse-of-*`, `distributivity`, `<-on-others`, `zero`, `trichotomy`, `positive`, `rational-implies1`, `rational-implies2`, `integer-implies-rational`, `complex-implies1`, `complex-definition`, `nonzero-imagpart`, `realpart-imagpart-elim`, `realpart-complex`, `imagpart-complex`, `integer-0`, `integer-1`, `integer-step`, `lowest-terms` |
| Characters (9) | `booleanp-characterp`, `characterp-page`, `characterp-tab`, `characterp-rubout`, `characterp-return`, `char-code-linear`, `code-char-type`, `code-char-char-code-is-identity`, `char-code-code-char-is-identity` |
| Strings (3) | `coerce-inverse-1`, `coerce-inverse-2`, `character-listp-coerce` |
| Symbols and packages (14) | `stringp-symbol-package-name`, `symbolp-intern-in-package-of-symbol`, `symbolp-pkg-witness`, `intern-in-package-of-symbol-symbol-name`, `symbol-name-pkg-witness`, `symbol-package-name-pkg-witness-name`, `symbol-name-intern-in-package-of-symbol`, `symbol-package-name-intern-in-package-of-symbol`, `intern-in-package-of-symbol-is-identity`, `symbol-listp-pkg-imports`, `no-duplicatesp-eq-pkg-imports`, `completion-of-pkg-imports`, `string-is-not-circular`, `nil-is-not-circular` |
| Values outside the guards (18) | `completion-of-symbol-name`, `completion-of-symbol-package-name`, `completion-of-+`, `completion-of-*`, `completion-of-unary-minus`, `completion-of-unary-/`, `completion-of-<`, `completion-of-car`, `completion-of-cdr`, `completion-of-char-code`, `completion-of-code-char`, `completion-of-complex`, `completion-of-coerce`, `completion-of-denominator`, `completion-of-imagpart`, `completion-of-intern-in-package-of-symbol`, `completion-of-numerator`, `completion-of-realpart` |
| Objects that are not data (4) | `booleanp-bad-atom<=`, `bad-atom<=-antisymmetric`, `bad-atom<=-transitive`, `bad-atom<=-total` |

In a proof these names are written as symbols of the package `ACL2`, in upper case: `ACL2::CAR-CONS`.

## 4. The facts a proof may cite

At any line, the facts are these, and no others.

| Fact | Name | Clause |
|---|---|---|
| A `clause` line of the ground theory | Its name | Its literals. |
| A definition: of the ground theory, of an admitted `define` statement, or of a `define` entry of the proofs | The function's name | The one literal `(equal (f x1 ... xn) body)`, with the formals and the body of the definition. |
| A formula of an admitted `constrain` statement | The formula's name | The one literal that is the formula. |
| An admitted `choose` statement, or a `choose` entry of the proofs | The function's name | The one literal that is its axiom (section 6). |
| An admitted `theorem` or `axiom` statement | Its name | The one literal that is its formula. |
| An admitted `package` statement, and the four packages of the ground theory for which ACL2 has an axiom | The name of ACL2's rule for the package, `NAME-PACKAGE` (`language.md`, section 6) | The one literal `(equal (pkg-imports '"NAME") 'imports)`. |
| A `lemma` entry of the proofs whose proof was checked | Its name | The literals the entry states. |

A statement's facts are added when the statement and its entry have been checked, not before; those of a given statement of the library, when its `skip` has been read or, where the library's proofs have ended, when its line has been admitted. So the proof of a theorem cannot cite the theorem, and the proofs of termination of a definition cannot cite its equation. Here and below, "the proofs" are the third input for a statement of the second, and the fourth for a statement of the library.

## 5. The rules

A proof is a sequence of steps. Each step applies one rule to the conclusions of earlier steps, its **premises**, and to the data on its line, and has a clause as its **conclusion**. If a condition of the rule does not hold, the step fails. Every term on a step's line must be a term (`language.md`, section 5).

There are eight rules. `C` and `D` stand for clauses, and `++` joins two lists of literals.

| | Rule | Premises | Data | Conclusion |
|---|---|---|---|---|
| 1 | `fact` | none | a name | the clause of the fact with that name |
| 2 | `instantiate` | `C` | a substitution `s` | `C` with `s` applied to every literal |
| 3 | `subsume` | `C` | the literals of a clause `D` | `D` |
| 4 | `cut` | `(a . R1)` and `((not a) . R2)` | none | `R1 ++ R2` |
| 5 | `substitute` | `((equal a b) . R1)` and `C` | a place in `C` | `C` with the term at that place, which is `a`, replaced by `b`; then `++ R1` |
| 6 | `beta` | none | a lambda application `t` | `((equal t body'))`, where `body'` is the body with the actuals put for the formals |
| 7 | `compute` | none | a call `t` of a primitive on constants | `((equal t 'v))`, where `v` is the value of the call |
| 8 | `induct` | two clauses, given below | a formula, a measure, substitutions | the clause of the formula |

For each rule: its conditions, and why its conclusion is true whenever its premises are. "True" means true as section 2 defines it, for the functions in use, whatever functions satisfy the facts.

**1. `fact`.** The name must be the name of a fact at this line (section 4). *Sound* because every fact is an axiom, or follows from the facts before it (section 9).

**2. `instantiate`.** The data is a list of pairs `(v t)`: the `v` are distinct variables and the `t` are terms. *Sound* because a clause claims something for every value of its variables, and so for the values of the terms `t`. Nothing is captured, since the body of every lambda is closed.

**3. `subsume`.** Every literal of `C`, other than the constant `'nil`, must be among the literals of `D`. This one rule weakens a clause, reorders it, removes a repeated literal, and removes a literal `'nil`. *Sound* because under any values some literal of `C` is not `NIL`; it is not the constant `'nil`; so it is a literal of `D`.

**4. `cut`.** The first literal of the second premise must be `(not a)`, where `a` is the first literal of the first premise, and `not` is the function of the ground theory. *Sound*: take any values. If `a` is `NIL`, the first premise gives a literal of `R1` that is not `NIL`. If `a` is not `NIL`, then `(not a)` is `NIL` by the definition of `not`, and the second premise gives a literal of `R2`.

**5. `substitute`.** The first literal of the first premise must be a call of `equal`, on `a` and `b`. The place is a number `I`, which picks the `I`-th literal of `C`, and then zero or more numbers, each of which picks an argument of a call or an actual of a lambda application. A place never enters a constant, the body of a lambda, or the position of a function, and a number that picks nothing fails. The term at the place must be exactly `a`. *Sound*: take any values. If a literal of `R1` is not `NIL`, the conclusion holds. Otherwise `a` and `b` have the same value, and a function gives the same value on the same arguments, so the literal has the same value after the replacement as before; and `C` holds.

**6. `beta`.** The data must be a lambda application. *Sound* because that is what a lambda application means in ACL2's logic: it is how ACL2 gives meaning to `let`.

**7. `compute`.** The data must be a call `(f 'c1 ... 'cn)` of a primitive function of `n` arguments on constants, and not one of the calls that are not computed (`language.md`, section 4). `v` is the value that the table of `language.md`, section 3, gives. *Sound* because that value is the one the axioms fix (section 9, step 5). This rule is also how a proof obtains the axiom of a declared package: `(compute (pkg-imports '"NAME"))`.

**8. `induct`.** The data is a term `phi`, a term `m`, and a list of substitutions `s1`, ..., `sk`, where `k` may be 0. Write `t/s` for a term `t` with a substitution `s` applied. The two premises must be exactly these clauses:

1. `((o-p m))`: the measure is an ordinal.
2. `((not (if (o< m/s1 m) phi/s1 't)) ... (not (if (o< m/sk m) phi/sk 't)) phi)`: `phi` holds if it holds at every one of the `k` substitutions at which the measure is smaller.

The conclusion is `(phi)`. *Sound*: this is ACL2's principle of induction with a single case. It rests on one fact outside the logic, which ACL2 rests on too: among the objects that `o-p` recognizes, which are the ordinals below ε<sub>0</sub>, there is no infinite sequence that descends by `o<`. Suppose `phi` were `NIL` under some values. Among all such values, take some for which the value of `m` is least; one exists, because every value of `m` is an ordinal by the first premise. By the second premise, some literal `(not (if (o< m/si m) phi/si 't))` is not `NIL` under those values, so `(o< m/si m)` is not `NIL` and `phi/si` is `NIL`. Then `phi` is `NIL` under the values that give each variable the value of what `si` puts for it, and under those the value of `m` is smaller. That contradicts the choice.

ACL2 states its principle with several cases, each with a test and its own substitutions and with the measure shown to decrease under the test. A proof in that form is turned into this one by a case split inside the proof of the second premise.

**Why these eight.** `fact` brings in what is known, `instantiate` and `substitute` are the two rules of equality and variables, `subsume` and `cut` are the propositional rules, `beta` gives the meaning of the one binding form, `compute` gives the values of the primitives on constants, and `induct` is the only rule that is not a rule of first-order logic. Every other step of reasoning, such as modus ponens, case analysis, the symmetry of `equal` and the opening of a definition, is a short sequence of these. Larger steps are the work of the last step of `PLAN.md`, where each is to be justified by a proof in these eight.

## 6. Admitting statements

Each line of the library, of the statements, and each `define`, `lemma` and `choose` entry of the proofs, is **admitted** only if it meets the conditions of its kind. A statement of the second input that has obligations is admitted only with its entry; a statement of the library that has obligations is admitted with its entry, or, where the library's proofs have ended, without one, as given (section 7). In the conditions, "new" means not in use, and the names a line introduces must also differ from one another. What may be a name, and a function name, is said in `language.md`, section 6.

A statement with obligations is taken in this order. When its line is read, its names stop being new, but its functions are not yet in use. The `define`, `lemma` and `choose` entries that stand before its own entry are admitted next, so none of them can take one of its names or call one of its functions. Then its own entry is read and its proofs are checked. Only then do its facts become facts. A statement of the library is taken in the same order; where the library's proofs have ended, it has no entry, and its facts become facts as soon as its line is admitted.

### `package`

`(package NAME IMPORTS)` is admitted when:

1. `NAME` is a string that is not empty, and no package of that name is declared, unless a `hidden-package` statement declared it with exactly these imports;
2. `IMPORTS` is a list of symbols, each of which exists, by the declarations before this line;
3. no two of the imports have the same name;
4. no import has the name `ACL2-PKG-WITNESS`;
5. the imports stand in the order of their names, each name before the next by `string<`, which compares the codes of the characters in turn and puts a name before every longer name that begins with it; this is the order in which ACL2 holds the imports of every package that `defpkg` declares;
6. `NAME` has no lower-case letter `a` to `z`, is not `"LISP"`, and does not begin with `ACL2_*1*_`.

It declares the package, brings the name of its rule into use, which must be new, and adds its fact under that name (section 4). It has no obligation, and it is never counted. A package of the ground theory is declared, so a `package` statement of it is refused, even one that is, byte for byte, a line of the ground theory, which is no input and so is not an earlier line ("A line that repeats an earlier one", below). ACL2 accepts such a `defpkg` as redundant; whether to follow it is undecided (`EDGE-CASES.md`, entry 7.1; `PLAN.md`).

**Why it may be assumed.** Until a package is declared, the axioms leave open what it imports. Take all the declarations of an input together, and let every package that none of them declares import nothing. Let the symbols be the pairs of a package name and a name that the rule of existence then allows, with `intern-in-package-of-symbol`, `pkg-imports` and `pkg-witness` as `language.md` defines them. Conditions 2 to 4 are what ACL2's axioms about symbols ask of a list of imports: its members are symbols (`symbol-listp-pkg-imports`), no two are the same (`no-duplicatesp-eq-pkg-imports`), an imported name leads to one symbol (`intern-in-package-of-symbol-is-identity`), and the symbol that `pkg-witness` gives for the package is the package's own (`symbol-package-name-pkg-witness-name`). With condition 4 dropped, those last two axioms would contradict each other. So the axioms are true of these symbols, with every package as declared. And a declaration never changes, because condition 1 lets no later line declare the package again: whatever a checker concluded from a declaration, or from the existence of a symbol, still holds at the end of the input.

Conditions 5 and 6 are not needed for that argument: they are ACL2's, so that a checker admits the packages that ACL2 admits and no others. ACL2 makes the same tests, and the checks record that it refuses a package that fails condition 3, 4 or 6, and that it sorts the imports and drops a repeated one (`EDGE-CASES.md`, entries 7.2 and 7.3). ACL2 also refuses the name of a package of the Lisp under it, and decides by the host whether a character with a code from 128 to 255 is lower case; ACL2 Core follows neither, because both depend on the host (entries 7.2 and 1.4).

### `hidden-package`

`(hidden-package NAME IMPORTS)` is admitted under conditions 2 to 6 of a `package` statement, when `NAME` is a string that is not empty and no package of that name is declared. It declares the package for the rule of existence, so that its symbols can be written, and for `intern-in-package-of-symbol`, which is computed at its symbols from the imports it declares. It does nothing else: it adds no fact and no name, `pkg-imports` and `pkg-witness` are not computed for it, and `symbol-package-name` is not computed for its symbols (`language.md`, sections 3 and 4; `EDGE-CASES.md`, entries 1.3, 2.8 and 2.9). A later `package` statement of the same name and the same imports makes the package an ordinary one.

This is what ACL2 does with a package that reaches its world only because a book that was included locally declared it. ACL2 must keep the package, because a symbol of it may stand in an event that remains; but it adds no axiom about its imports, and its evaluator treats the name as that of no package, while it interns at a symbol of the package from the imports it keeps and proves theorems by that. **Checked against ACL2:** the check certifies a book in a world that declares a package, and a second book that includes the first locally. In a world that includes the second book, ACL2 holds the package as hidden (the line `hidden-package`), refuses to evaluate `pkg-imports` and `pkg-witness` on its name (two lines `no-plain`), cannot prove what it imports, and accepts an open declaration of it with the same imports.

### `define`

`(define RULERS (F1 FORMALS1 BODY1) ... (Fk FORMALSk BODYk))` is admitted when:

1. `RULERS` is the symbol `KEYWORD::ALL` or a list of symbols;
2. each `Fi` is a new function name;
3. each `FORMALSi` is a list of distinct variables;
4. each `BODYi` is a term whose variables are all among `FORMALSi`, where, for this test, each `Fi` counts as a function in use with as many arguments as it has formals;
5. if some body calls one of the `Fi`: the obligations of termination below are proved, or the entry is `skip`, or the line is in the library and is given.

A body **calls** one of the `Fi` when a call of it stands in the body outside a constant, in which a list is data, and outside the executable half of an `mbe`, `a` in `(return-last 'mbe1-raw a b)`, which the walk below does not enter either. This is how ACL2 decides whether a definition is recursive: a definition whose only calls of its own functions are in executable halves has no obligations, and ACL2 holds its own `string-append`, which calls itself in the executable half of its `mbe`, as not recursive (`EDGE-CASES.md`, entry 6.2).

It brings the `Fi` into use and adds the equation of each as a fact.

**The obligations of termination.** They are ACL2's measure conjectures. The entry `(measure F1 M1 ... Mk)` gives a **measure** for each function: `Mi` is a term whose variables are among `FORMALSi` and whose functions are in use when the entry is read. The `Fi` are not yet in use then, so no measure calls one of them. The obligations are clauses, in this order: first `((o-p Mi))` for each `i` in order; then, for each `i` in order, one clause for each call that the following walk of `BODYi` records, in the order in which it records them. A clause that is the same as an earlier one is left out, and does not count toward the budget of `formats.md`, section 8.

**The walk** is ACL2's termination machine. It goes through a term with a list of **rulers**, at first empty, and a substitution, at first the identity. A ruler is a term with a sign. `RULERS`, the ruler-extenders of the statement, says where the walk looks for tests: a function `g` **extends the rulers** if `RULERS` is `KEYWORD::ALL` or `g` is a member of it, and lambdas extend them if `RULERS` is `KEYWORD::ALL` or `KEYWORD::LAMBDAS` is a member of it.

- A variable or a constant: nothing.
- A lambda application: if lambdas extend the rulers, walk each actual in order; otherwise record the calls in the actuals. Then walk the body with the same rulers and with the substitution that puts, for each formal, the actual with the present substitution applied.
- `(if a b c)`: if `if` extends the rulers, walk `a`; otherwise record the calls in `a`. Then walk `b` with the ruler `a'`, positive, added at the end of the list; then walk `c` with the ruler `a'`, negative, added at the end. Here `a'` is `a` with the substitution applied.
- `(return-last 'mbe1-raw a b)`, a call of `return-last` whose first argument is the constant `ACL2::MBE1-RAW`: walk `b` only. This is an `mbe`, and `a` is its executable half.
- Any other call `(g a1 ... an)`: if `g` extends the rulers, record the call itself if `g` is an `Fj`, and then walk each argument in order. Otherwise record the calls in the whole term.

To **record the calls** in a term is to record, with the present rulers and no others, every call of an `Fj` in the term, at any depth outside a constant: a call before the calls in its arguments, and the arguments in order; for a lambda application, the calls in its actuals and then those in its body, under the substitution that puts, for each formal, the actual with the present substitution applied; for `(return-last 'mbe1-raw a b)`, only those in `b`. A variable records nothing: a call in an actual is recorded once, from the actual, and not again at each occurrence of its formal in the body, which would give the same clause again and could take time exponential in the nesting of lambdas. ACL2's termination machine records the calls so (its function `all-calls`). A test of an `if` inside the term rules none of these calls.

A call `(Fj a1 ... an)` recorded in `BODYi` under the rulers `r1`, ..., `rp` gives the clause

```
(L1 ... Lp (o< Mj' Mi))
```

where `Mj'` is `Mj` with, for each formal of `Fj`, the argument `a` of the call with the substitution of that moment applied; and where `L` is `(not r)` for a positive ruler `r`, and `r` itself for a negative one. The clause says: if every ruler holds with its sign, the measure of the called function at the arguments of the call is below the measure of the calling function.

Once the measures are read, the `Fi` are in use, because the obligations may mention them and so their proofs must; but their equations are not facts until the last proof is checked.

**This is what ACL2 asks.** The walk records the calls that ACL2's termination machine records, each under the tests that ACL2 puts on it. ACL2 uses the ruler-extenders that the definition declares, or its default, the list `(if mv-list return-last)`, and stores them with the definition; the exporter writes what ACL2 stored. So ACL2 Core asks, of each definition, for what ACL2 asked: it admits what ACL2 admits, and it measures every call that ACL2 measures. ACL2 writes its conjectures in a tidier form than the clauses above: it strips from a test the functions that only carry guards, drops a test that a later one implies, folds a call of a primitive on constants, and negates by removing a `not` where it can. Each of these keeps a clause equivalent, and ACL2 Core does none of them: they would be more to implement and to trust, and would change no verdict. The measure and the relation are no part of a `define` statement: any measure for which the obligations are proved admits the same equations.

**Checked against ACL2.** The check holds the walk as a program, and at the places where ACL2 tidies a test or a call it applies ACL2's own functions for that. For every one of the 523 definitions of the world ACL2 8.7 starts with that call themselves, under the four different ruler-extenders ACL2 stores for them, the walk then records exactly the calls and tests of ACL2's termination machine (the line `agrees`). The lines `rulers` and `obligation` show the obligations of four definitions; ACL2 refuses `bm-r0`, whose recursion is ruled only by a test inside an argument of `cons`, under its default, and admits the same body as `bm-r1` with the ruler-extenders `:all`; it refuses `bm-g0`, a recursion in the first argument of `prog2$` that does not end; and it admits `bm-g1`, whose `mbe` has a recursive call in its executable half that no clause measures.

**Why the equations may be assumed.** This is ACL2's definitional principle. The measure conjectures hold whatever the `Fi` are, since their proofs use no fact about the `Fi`. Define each `Fi` by recursion on the ordinal value of its measure: its value at given arguments is the value of its body, where a call of an `Fj` at arguments whose measure is not smaller counts as `NIL`. That recursion is well founded, so it defines functions. They satisfy the equations: go through a body in the order of the walk. A call recorded under rulers that all hold has, by its clause, a smaller measure, so it has its true value. A call under a ruler that does not hold stands in the branch of an `if` that is not taken, so its value does not matter. The executable half of an `mbe` does not matter, because `return-last` gives its last argument. When no body calls one of the `Fi`, in the sense above, no measure is needed: each body, whose only calls of the `Fi` stand in executable halves that do not matter, defines its function outright. So adding the equations cannot make false anything about the functions that were there before.

**Why every run ends.** A runner evaluates a call only when it has evaluated the tests of every `if` above it and found the branch taken (`language.md`, section 4), and it never evaluates the executable half of an `mbe`. So the rulers of a call that it evaluates all hold, the clause of that call says that the measure falls, and no computation goes on for ever.

**A definition that ACL2 admits with another relation.** ACL2 lets a definition name a relation other than `o<`, with `:well-founded-relation` among its declarations. The relation `rel` must first be shown well founded on the objects that a recognizer `mp` accepts, by a theorem that ACL2 is given as a rule of the class `:well-founded-relation`. The theorem names a function `fn` that embeds those objects in the ordinals:

```
(and (implies (mp x) (o-p (fn x)))
     (implies (and (mp x) (mp y) (rel x y))
              (o< (fn x) (fn y))))
```

ACL2 also takes the form with no recognizer, `(and (o-p (fn x)) (implies (rel x y) (o< (fn x) (fn y))))`, and it lets a relation have one such rule only. For a measure `m`, ACL2's conjectures are then `(mp m)` and, for each recursive call, that under its tests `(rel m' m)` holds, where `m'` is the measure at the arguments of the call.

**ACL2 Core gives such a definition no place of its own, and needs none.** A `define` statement carries neither a measure nor a relation, so the statement is the same whatever ACL2 used. The obligations of this section, which are stated with `o<`, are met by the measure `(fn m)`:

- `(o-p (fn m))` follows from `(mp m)` and the first half of the theorem;
- for a call, `(mp m')` is an instance of `(mp m)`, and under the rulers `(rel m' m)` holds, so the second half of the theorem gives `(o< (fn m') (fn m))`.

The theorem of the relation is a `defthm` of a book like any other. It becomes a `theorem` statement, which the proofs of the obligations cite as a fact; its rule class, like every rule class, is no part of the statement. So no definition is outside ACL2 Core because of its relation, and a checker never meets one: it sees a `define` statement and an entry that gives a measure.

ACL2 8.7 starts with two relations: `o<` on the objects `o-p` recognizes, and `l<` on those `lexp` recognizes. For `l<` its world holds no theorem of the name `well-founded-l<`. ACL2's source file `boot-strap-pass-2-b.lisp` quotes the theorem, `well-founded-l<`, with the embedding `ltoo`, from the book `ordinals/lexicographic-book.lisp` that is distributed with ACL2. A proof about a definition that ACL2 measured with `l<` takes the embedding from the statements of that book, or defines one of its own.

**Checked against ACL2.** The check defines a relation, proves the theorem above for it, and has ACL2 admit a definition with it. It records the recognizer, the relation and the measure that ACL2 stores for the definition, and ACL2's termination theorem, which has the form given. It computes the obligations of this section for the embedded measure, by the walk above, and ACL2 proves each of them from its own termination theorem and the theorem of the relation, with the definitions of the relation, the recognizer and the embedding disabled. ACL2 refuses a rule of the class without the first conjunct, a second rule for one relation, and a definition that names a relation with no rule. These are the lines `well-founded`, `stored-theorem`, `justification`, `termination` and `obligation` of `checks/expected/facts.txt`, and six of its lines `accepted` and `refused`.

### `constrain`

`(constrain ((F1 N1) ... (Fk Nk)) ((NAME1 TERM1) ... (NAMEm TERMm)))` is admitted when:

1. each `Fi` is a new function name, and each `Ni` is an integer that is not negative;
2. each `NAMEj` is a new symbol;
3. each `TERMj` is a term, where, for this test, each `Fi` counts as a function in use with `Ni` arguments;
4. if `m` is not 0: the obligations below are proved, or the entry is `skip`, or the line is in the library and is given.

It brings the `Fi` into use, and adds each formula as a fact under its name.

**The obligations.** The entry `(witness F1 G1 ... Gk)` names, for each `Fi`, a function `Gi` that is in use when the entry is read and has `Ni` arguments. The `Fi` are not in use then, so no witness is, or is defined with, one of them; nor are they while the proofs of the entry are checked, since its obligations name the witnesses and not the `Fi`. They come into use, with the formulas as facts, when the last of those proofs is checked or at the `skip`. The obligations are the clauses `(TERMj')` for each `j` in order, where `TERMj'` is `TERMj` with the name of every call of an `Fi` replaced by `Gi`, at any depth: in the arguments of calls, in the actuals of lambda applications and in the bodies of lambdas. Nothing inside a constant is replaced: a constant is data. A witness that is not yet a function is first defined by a `define` entry of the proofs, or introduced by a `choose` entry.

**Why the formulas may be assumed of functions with no definition.** The functions `Gi` exist and satisfy the formulas. So whatever functions are in use before the statement, there are functions for the `Fi` that make every formula true: the `Gi`. Any proof that uses the formulas is therefore a proof about some functions that exist, and a conclusion of it that does not mention the `Fi` does not depend on the choice. This is ACL2's principle for `encapsulate`: the local definitions of the book are the witnesses, and they are needed only to show that the constraint can be met.

### `choose`

`(choose F BOUND FREE BODY FREE2)` is admitted when:

1. `F` is a new function name;
2. `BOUND` is a list of one or more distinct variables, `FREE` is a list of distinct variables, and no variable is in both;
3. `BODY` is a term whose functions are in use and whose variables are all in `BOUND` or `FREE`;
4. `FREE2` is `NIL`, or a list of distinct variables, as many as `FREE` has, none of which is in `BOUND` or `FREE`.

It brings `F` into use, with as many arguments as `FREE` has variables, and adds one fact under the name `F`. It has no obligation. The fact's one literal is built as follows. Let `call` be `(F x1 ... xn)`, with the variables of `FREE`. Let `s` put, for the variables of `BOUND`: if there is one, `call`; if there are several, `(mv-nth '0 call)`, `(mv-nth '1 call)` and so on.

- With one bound variable, `basic` is `(implies BODY BODY/s)`.
- With several, `basic` is `(if (true-listp call) (implies BODY BODY/s) 'nil)`.
- If `FREE2` is `NIL`, the literal is `basic`.
- Otherwise let `call2` be `(F y1 ... yn)`, with the variables of `FREE2`; let `s2` be as `s`, with `call2`; let `BODY2` be `BODY` with each variable of `FREE` replaced by the variable of `FREE2` at the same position; and let `d1` be `(equal call call2)`, `d2` be `(if BODY/s (not BODY2/s) 'nil)` and `d3` be `(if BODY2/s2 (not BODY/s2) 'nil)`. The literal is `(if basic (if d1 d1 (if d2 d2 d3)) 'nil)`.

When `FREE` has no variable, `FREE2` is `NIL`, and nothing is lost: the longer axiom would add only that `(F)` equals itself.

The basic axiom says: if any values of the bound variables make the body true, the values that `F` gives do. The longer one, which ACL2 adds for `defchoose` with `:strengthen t`, says besides that `F` gives the same values wherever the same values make the body true. **Why it may be assumed:** fix an order of all objects in which every set that is not empty has a least member. Let `F` give the least value, or the least list of values, that makes the body true, and `NIL` where none does. That function satisfies both forms of the axiom. This is ACL2's principle for `defchoose`, and the argument uses the axiom of choice outside the logic, as ACL2's does. **Checked against ACL2:** for four `defchoose` events, with one and with two bound variables, each with and without `:strengthen t`, the axiom ACL2 stores is the literal above, once every lambda application in ACL2's axiom is replaced by its body with the actuals put for the formals. These are the lines `(choose NAME COMMON-LISP::T)` of `checks/expected/facts.txt`.

### `theorem` and `axiom`

`(theorem NAME TERM)` is admitted when `NAME` is a new symbol, `TERM` is a term whose functions are in use, and either the entry `(theorem NAME)` is followed by a proof of the clause `(TERM)`, or the entry is `(skip NAME)`, or the line is in the library and is given. It adds the formula as a fact.

`(axiom NAME TERM)` is admitted when `NAME` is a new symbol and `TERM` is a term whose functions are in use. It adds the formula as a fact, with no obligation, and the verdict counts it: among the assumed if it is a statement of the book, and among the given facts if it is in the library.

### `reserve`

`(reserve NAME)` is admitted when `NAME` is a new name. It brings the name into use and adds nothing else. ACL2 holds a macro, a constant, a label, a theory or a single-threaded object under such a name, and refuses any later event that would take it; the check records its refusal for a macro and for a constant.

### A line that repeats an earlier one

A line of the library or of the statements that is, byte for byte, an earlier line of either is admitted without being tested again. It adds nothing, has no obligation and is not counted. ACL2 does the same with an event that repeats one it has.

### Entries of the proofs

A `define` entry is admitted exactly as a `define` statement of a book. If some body calls a function of the entry, the next entry must be its `measure`, with proofs of its obligations, or its `skip`, which the verdict counts among the skipped.

`(lemma NAME L1 ... Ln)` is admitted when `NAME` is a new symbol, there is at least one literal, each literal is a term whose functions are in use, and the proof that follows proves the clause. It adds the clause as a fact. A lemma is never skipped: it is the proof's own claim.

A `choose` entry is admitted exactly as a `choose` statement of a book, and adds the same fact under the same name. It has no obligation and the verdict does not count it: its axiom may be assumed for the reason given for the statement.

A `choose` entry is how a proof meets a constraint that only a choice function meets, as that of a `defun-sk` is. ACL2 introduces the function of a `defun-sk` and its witness with an `encapsulate`, and proves the constraint, inside it, from a `defchoose` that is local to it; the `constrain` statement holds the constraint and not the `defchoose`. Its proof does what ACL2 did: a `choose` entry introduces a function by the `defchoose`, a `define` entry defines the other function from it where one is needed, the `witness` entry names the two, and the proofs derive the formulas from the axiom of choice (`EDGE-CASES.md`, entry 6.9).

Definitions, lemmas and functions chosen in the proofs add nothing that could not be had without them. A lemma stands for its proof. A definition, or a function introduced by choice, is admitted by the same principle as a statement's, so it leaves everything about the other functions as it was. They are how the local events of a book reach a proof, and why ACL2 Core has no statement for `local`.

## 7. The library

The first input holds statements that are taken as given unless the fourth input proves them. For now it is ACL2's own built-in library: every function in logic mode that ACL2 has before it reads a book, other than those of the ground theory, the theorems ACL2 holds about them, and a `reserve` line for every other name ACL2 has in use, written by ACL2 from its own world (`PLAN.md`, step 2). The library is where ACL2's own functions of the package `COMMON-LISP` are defined, which no book may define (`language.md`, section 6).

**What ACL2 starts with.** The world of ACL2 8.7, before it reads a book, holds 1,489 functions defined in logic mode, the 37 of the ground theory among them. Among the 1,489 are 40 cliques of more than one function, each of which is one `define` statement. The world also holds 162 functions in logic mode that have no definition and are not primitive. An `encapsulate` event introduced every one of them, and for 40 of them ACL2 stores no constraint. They become `constrain` statements, with the formulas ACL2 stores as their constraints, which are the facts about them. 68 of the 162 have an attachment, a function that ACL2 runs in their place. An attachment is no part of the logic and becomes no statement (`language.md`, section 4). One of the 1,489 defined functions, `apply$-equivalence`, which `defun-sk` defines, has its equation in the constraint of the `encapsulate` that introduced its witness: it is a function of that `constrain` statement and has no `define` statement (`EDGE-CASES.md`, entry 6.6).

**The order of the library.** A body may call only functions that are in use, so the definitions of the library stand in an order in which each comes after every function that its body calls. Such an order exists for the 1,489: the check places them all. No order could also put each definition after the functions that ACL2's own measure for it calls. ACL2 measures `len` by `acl2-count`, the body of `acl2-count` calls `length`, and the body of `length` calls `len`. For five definitions, `apply$` and `ev$` among them, ACL2 stores no measure at all, only the formals that a measure would depend on. A `define` statement carries no measure, so the order of the library follows the bodies and nothing else; a measure is given later, by the proof, from the functions then in use. These are the lines `count`, `measure` and `calls` of `checks/expected/facts.txt`.

A line of the library is admitted when it meets every condition of its kind except the obligations. So a given statement is well formed: its names are new, its terms are terms, its symbols exist. What is not shown is that its recursion ends, that its constraint can be met, or that its theorem follows.

**The library's proofs.** The fourth input holds proofs of statements of the library, in the form of the proofs of a book (`formats.md`, section 6). The checker reads it beside the library (`formats.md`, section 7). A statement of the library that has obligations is proved as a statement of a book is: by its `theorem`, `measure` or `witness` entry and the proofs that follow, from the facts that stand before it. One whose entry there is a `skip`, or that the checker reaches after the library's proofs have ended, is given. A proved statement of the library differs from a statement of a book in one thing: it is a line of the library, so it may define a function whose name is a symbol of `COMMON-LISP`, as ACL2's own definitions of `nth` and `expt` do, which no book may (`language.md`, section 6). The entries of the library's proofs are entries of proofs like any others: a function that one of them defines or chooses is not named by a symbol of `COMMON-LISP`, and every name that one of them takes is in use from then on, for the statements of the book too.

The verdict counts what was given (`formats.md`, section 9). A statement is given because it came on the first input and the fourth does not prove it, and nothing in a book can change that (`formats.md`, section 5). When the fourth input proves every statement of the library that has obligations, and the library has no `axiom`, the counts of the given are 0.

## 8. An example

[`example/statements.txt`](example/statements.txt) holds one statement, the theorem `(equal x x)`, and [`example/proofs.txt`](example/proofs.txt) proves it from the ground theory. Here are its steps, with the conclusion a checker computes for each, in ACL2's usual print.

| Step | Line | Conclusion |
|---|---|---|
| 1 | `(fact "non-nil-true")` | `((equal x 'nil) x)` |
| 2 | `(instantiate 1 ((x (equal x x))))` | `((equal (equal x x) 'nil) (equal x x))` |
| 3 | `(fact "equal-same")` | `((equal (equal x x) 't))` |
| 4 | `(substitute 3 2 1 1)` | `((equal 't 'nil) (equal x x))` |
| 5 | `(compute (equal 't 'nil))` | `((equal (equal 't 'nil) 'nil))` |
| 6 | `(substitute 5 4 1)` | `('nil (equal x x))` |
| 7 | `(subsume 6 (equal x x))` | `((equal x x))` |

Step 4 replaces, in the first literal of step 2, its first argument, which is the left side of the equality of step 3. Step 6 replaces the whole first literal of step 4. Step 7 drops the literal `'nil`. The last conclusion is the clause of the theorem, so the verdict on the two files, with an empty library, is `accepted`. The check has ACL2 prove the conclusion of each of the seven steps (the lines `(accepted "example step N")` of `checks/expected/facts.txt`). No checker exists yet to run on the example; step 4 of `PLAN.md` builds the first.

## 9. The argument for the verdict

The claim of section 1 follows from seven steps. Each can be attacked on its own.

**Step 1. An input has one reading.** Each datum has exactly one text and each text one datum (`formats.md`, section 2), and a line is a word and data. So two checkers that are given the same bytes hold the same statements and the same steps, and a reader who looks at a statement sees what the checker sees.

**Step 2. Every symbol a checker holds is an object, and the checker knows its name and its package.** A symbol reaches a checker in three ways.

- *It is written on a line.* The rule of existence (`language.md`, section 2) was applied to it: its package `P` is declared, openly or as a hidden package, and `P` imports no symbol of its name `N`. By the axiom `symbol-package-name-intern-in-package-of-symbol` and the imports of `P`, interning `N` in `P` gives a symbol whose package name is `P`; by `symbol-name-intern-in-package-of-symbol` its name is `N`; and by `intern-in-package-of-symbol-symbol-name` there is one such symbol. The text `P::N` denotes that object.
- *It is in the ground theory.* The same holds, by the five packages of the ground theory.
- *`compute` made it.* Only `intern-in-package-of-symbol` and `pkg-witness` give a symbol that is not `T`, `NIL` or part of an argument. The first is computed only for a symbol of a package that is declared, openly or as a hidden package, and gives an import of that package, which exists because a `package` or `hidden-package` line is admitted only if its imports exist, or a symbol of the package with a name it does not import, which exists by the rule of existence. The second is computed only for a package that is declared openly, whose imports have no symbol named `ACL2-PKG-WITNESS`, or, for an argument that is not a string, gives `ACL2::ACL2-PKG-WITNESS`.

Without the rule, a checker could be given `P::N` where `P` imports a symbol `Q::N`. ACL2's axioms say that interning `N` in `P` gives `Q::N`, so no object has the package name `P` and the name `N`. A checker that held `P::N` as an object apart from `Q::N` would compute `(equal 'P::N 'Q::N)` to `NIL` and `(symbol-package-name 'P::N)` to `"P"`, and from those and the axioms it would derive `NIL`. The rule does not rest on who wrote the declarations: it is applied to every symbol against the declarations that the same input makes, and section 6 shows that any declarations that are admitted can be assumed.

**Step 3. Every fact of the ground theory is one that ACL2 holds.** The 80 named axioms and the four that are packages are ACL2's `defaxiom` events, read from ACL2's world. The 37 definitions are ACL2's. The 23 built-in clauses are read from ACL2's own constant: ACL2 takes them as true without proof, and so does ACL2 Core (section 3). ACL2 proves the 41 others, and those 23 too, each as the disjunction of its literals. The `specials` line is ACL2's own list. The fifth package is discussed in section 10. The check confirms all of this, and that `ground.txt` is byte for byte what ACL2 writes.

**Step 4. Each rule gives a true conclusion from true premises.** Section 5 argues this for each of the eight. Two things are used from outside: that a lambda application means its body with the actuals put for the formals, and that `o<` is well founded on the ordinals that `o-p` recognizes. ACL2's logic rests on both. The built-in clauses of step 3 add a third thing that ACL2's logic rests on and no axiom states: that the conses are well founded.

**Step 5. `compute` gives the value the axioms fix.** A constant stands for the object it writes: an integer for itself, built from 0 and 1 by `binary-+` and `unary--`; a fraction for its numerator times the reciprocal of its denominator; a complex rational for `complex` of its parts; a character for `code-char` of its code; a string for `coerce` of the list of its characters; a symbol for the interning of step 2; a cons for `cons` of its parts. For each primitive, the value in the table of `language.md` is the one that ACL2's axioms give to such objects: the axioms named `completion-of-` give the values outside the guards, and the rest are the arithmetic of the rationals and of the complex rationals, the pairing of characters with codes, the pairing of strings with lists of characters, and the axioms about symbols. The calls that ACL2's evaluator refuses are not computed. In two places the value rests on what ACL2 does and not on an axiom: `bad-atom<=` on data, for which ACL2's evaluator gives `NIL`, and `intern-in-package-of-symbol` at a symbol of a hidden package, which ACL2's evaluator computes from the imports it keeps; ACL2 proves theorems by both (section 10). For the second, step 6 shows that every package of an input, a hidden one among them, can import what it declares while the axioms hold. The check records ACL2's own value for 157 calls, and they are the table's. That a checker's own arithmetic is right is a matter of its code, which is why two checkers are to be written apart and compared.

**Step 6. Each admission adds only what can be assumed.** Section 6 argues it for each kind. The packages of an input, the hidden ones among them, can all be as declared, together, with ACL2's axioms about symbols true of them. A `reserve` line and a repeated line add nothing. A definition whose obligations are proved has a function that satisfies it; a constraint whose witnesses are shown is met by them; a choice axiom, of a statement or of an entry of the proofs, is met by a least-value function. In each of those three the functions that were there before keep their meaning, so nothing about them becomes provable that was not already true of them. Whatever is admitted without its obligation, by `skip`, by `axiom` or as a given statement of the library, is counted.

**Step 7. The checker's bookkeeping lets nothing else in.** A fact enters the table in the seven ways of section 4 and no other. Names are never reused, so the name on a `fact` step means one fact. A term is checked before it is used, so no step reasons about a function that is not in use or a call with the wrong number of arguments. `QUOTE` names no function, so a list that begins with it is always a constant, although `QUOTE` alone may be a variable; `T`, `NIL` and the keywords name no function and no variable (`language.md`, sections 5 and 6). So no term is read in two ways. A proof with no step proves nothing, and a proof proves only the clause its last step concludes. A statement of the second input with obligations needs its own entry, in order; a statement of the library with obligations needs its own entry too, in order, unless the library's proofs have ended; it is counted when that entry is a `skip` and when they have ended.

**Conclusion.** Go through the lines in the order a checker takes them. By steps 3 and 6, the facts present at any line are ACL2's axioms, the axioms that admitted statements add, and the counted assumptions, together with clauses that follow from those. By steps 2, 4, 5 and 7, each step of each proof concludes a clause that follows from the facts present. So every theorem follows from them. If the verdict is `accepted`, nothing was counted, and by step 6 the theory is the ground theory, with the packages as declared, extended only by functions that exist.

**What the argument does not cover.** That ACL2's axioms are consistent. That a checker's code does what this document says: the remedy is that it is small, that two are written apart, and that their verdicts are compared. And that the statements are what the book says: the remedy is that ACL2 writes them and that they are plain enough to read.

## 10. ACL2 Core and ACL2

ACL2 is the definition of ACL2. ACL2 Core follows what ACL2 does: its axioms, its evaluator, and the tests it makes before it admits an event. `EDGE-CASES.md`, at the root of the repository, lists every place found where what ACL2 does goes beyond, falls short of or differs from what its axioms say: for each, what ACL2 Core does, and where ACL2 Core does not follow ACL2, why. `sh checks/run.sh` confirms every entry. The places that wait on a decision are under "Undecided" in `PLAN.md`.

Four of those places bear on the claim of section 1, because there ACL2 computes and proves theorems with a fact that none of its axioms states, and ACL2 Core does the same:

1. **`bad-atom<=` on data is `NIL`** (`EDGE-CASES.md`, entry 1.1). The axioms order only the objects that are not data.
2. **`COMMON-LISP` imports nothing** (entry 1.2). ACL2's source says that it "pretends that no symbols are imported" into that package; the ground theory states it as its fifth `package` line.
3. **A hidden package imports what its statement declares** (entry 1.3). ACL2 states no axiom about a hidden package, but its evaluator interns at a symbol of one from the imports it keeps. By section 6, every package of an input, the hidden ones among them, can import what it declares.
4. **The conses are well founded** (entry 9.6). ACL2's prover takes 23 clauses about `acl2-count` as true with no proof, and admits `acl2-count` with its proof of termination skipped; the ground theory holds the 23 as facts (section 3).

## 11. What each mechanism buys

Every rule, kind of line and special case is something to implement twice and to trust. This table lists the ones a reader might think could be left out, with what each costs and what it buys. Section 5 does the same for the eight rules.

| Mechanism | What it costs | What it buys |
|---|---|---|
| Words that are not data | One more kind of token in the reader. | The format's own vocabulary is in no package, so a file can be read before any package exists, and no statement can collide with it. |
| One text for each datum, every symbol with its package | Longer files, and a reader that must reject every other spelling. | A reader with no table and no state; two exporters compared with `cmp`; a symbol whose text does not depend on any declaration. |
| The ground theory as a file of data | 219 lines that every checker holds. | The axioms are not code. ACL2 writes them, and the check compares every byte. |
| 36 facts beyond ACL2's axioms | 36 more clauses to believe, each proved by ACL2 in the check. | What ACL2's prover knows about its primitives without an axiom. Without them the kinds of object could not be told apart in a proof. |
| Clauses, not single formulas | Two notions, formula and clause. | Case analysis and hypotheses without wrapping every step in `if`; the propositional rules are two. |
| One statement, `define`, for one function and for several | Nothing. | One kind of statement fewer than ACL2's `defun` and `mutual-recursion`. |
| `define` and `lemma` entries in the proofs | Two kinds of entry, in the one space of names. | No statement for `local`, no scopes, and no `include-book` statement: what a book wrote for ACL2's prover is the proof's business. |
| A `choose` entry in the proofs | One more kind of entry, admitted by the conditions of the `choose` statement. | A proof of the constraint of a `defun-sk`, which ACL2 too proves from a local `defchoose`. Without it every such constraint could only be skipped or given. |
| A witness that is a function name, not a term | A `define` entry when the witness is not yet a function. | Putting the witness for the constrained function is a renaming, with no substitution into lambdas. |
| `FREE2` in `choose` | One datum. | ACL2's strengthened axiom of choice, without the checker inventing variables. |
| `true-listp`, `mv-nth` and `zp` in the ground theory | Three definitions. | ACL2's axiom of choice for several bound variables, exactly. |
| `acl2-count`, `integer-abs`, `length` and `len` in the ground theory | Four definitions taken as axioms. | The function by which ACL2 measures a recursion on conses. |
| ACL2's 23 built-in clauses about `acl2-count`, with the definition of `null`, which one of them mentions | 23 clauses that ACL2 assumes and does not prove, and one definition. | That `acl2-count` is a measure: without them no recursion on the `car` or the `cdr` of a cons could be shown to end. They are ACL2's own clauses, so a proof can cite what ACL2's prover would have found. |
| No measure and no relation in a `define` statement | The exporter writes them beside the book, where a prover finds them. | One statement for every definition, whatever measure and whatever well-founded relation ACL2 used, and a library whose order follows the bodies alone. |
| Ruler-extenders in a `define` statement, and ACL2's cases in the walk | One datum on each definition, and the five cases of the walk. | ACL2's own obligations: what ACL2 admits is admitted, every call ACL2 measures is measured, and every run ends. |
| `reserve` | One kind of statement, and a line in the library for each macro, constant, label and theory of ACL2. | ACL2's rule that a name is used once, for the names that have no logical content. |
| `hidden-package` | One kind of statement. | A symbol of a package ACL2 keeps hidden can be written, and nothing is claimed of the package that ACL2 does not claim. |
| The `specials` line of the ground theory | 122 symbols that every checker holds. | ACL2's rule for a variable, exactly. |
| A repeated line adds nothing | A comparison of lines. | ACL2's treatment of an event that repeats an earlier one. |
| `skip` | One kind of entry and one count. | A provisional verdict for every book before any proof exists, and a measure of what remains. |
| Four inputs | A second place where entries are read, and one more name of an input in a rejection. | What is given cannot be claimed from inside a book; and the library can be proved where it stands, with its definitions of functions of `COMMON-LISP`, which no book may define. |
| Two budgets, stated in sizes | The arithmetic of sizes in each checker. | Every check ends, and two checkers reject the same line. |
| A rejection that names a place | No symbol in the verdict. | No printer in a checker, and exact agreement on a rejection even when the line that fails has no readable name. |

**Left out on purpose.** There is no statement for the value of a constant, for `local`, for `include-book` or for a guard; no rule that evaluates a defined function; no rule that uses a theorem about constrained functions at other functions; no comment in any file. Each can be had from what is there: a constant is its value, a local event is a lemma or a definition of the proof, an included book is its statements, an evaluation is a proof by the rules, and the last two rules are among the larger steps of `PLAN.md`, step 8.
