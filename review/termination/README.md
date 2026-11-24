# The obligations of termination, compared with ACL2's

`PLAN.md`, step 5, asks for "for every definition, a comparison of the obligations of termination with ACL2's own measure conjectures". This directory holds that comparison. For every definition with obligations in the ground theory, in ACL2's built-in library and in the 460 books of `export/books.txt`, it gives the checker the measure that ACL2 holds for the definition, takes the clauses that the checker computes as its obligations of termination (`spec/logic.md`, section 6), and compares them, clause for clause and in order, with the measure conjectures that ACL2 generates for the same definition and measure. One command does it all, from the root of the repository:

```
sh review/termination/run.sh
```

Run on 2026-11-24, it printed "all compared definitions agree" (231 seconds). No definition has obligations that differ from ACL2's conjectures; the counts are under "The result".

## The files

| File | What it is |
|---|---|
| `run.sh` | The command. It builds the checker (`checker/build.sh`) and the book of the printer (`export/certify.sh`); runs `one.sh` on the library; certifies `cases.lisp` into `build/termination/`, exports it with `export/book.sh` and runs `one.sh` on it; runs `one.sh` on each book of `export/books.txt`, two at a time; and prints a line for the cases, the ground theory, the library and each book, and a last line that says whether every definition compared agreed. It writes the same to `build/termination/summary.txt`. With names of books as arguments, it does the library, the cases and those books only. It needs the files that `export/run.sh` writes. |
| `one.sh` | One run of ACL2 for one target: it includes the book, then the checker's books, the printer, the tool and the comparison, and writes `build/termination/library.txt` or `build/termination/books/BOOK.txt`, with a line for each definition (below), and beside it `.measures`, the measure and relation of each function in ACL2's world. |
| `obligations.lisp` | The tool: functions in the package of the checker, in program mode, that call the checker's own functions and give the clauses it computes as data. It is no part of the checker: it is not exported with it and not counted in its size. |
| `compare.lsp` | ACL2's side, the normal form and the comparison, in program mode. |
| `cases.lisp`, `cases.txt` | A book of eight recursive definitions, one for each way in which a definition can fail to agree exactly, and the class that each must have. |

## The checker's side

`obligations.lisp` is loaded after the book `build/checker/acl2/check`, as `checker/build.sh` certifies it, so that it runs the checker's own compiled functions.

- **The ground theory.** It reads `spec/ground.txt` with the checker's `load-ground`. For each of its define lines whose body calls its function, it calls `measure-entry` in the world of the whole ground theory. The checker never asks for these obligations, since the ground theory is taken as it stands; they are computed as for any other define.
- **The library.** It reads and admits `build/export/library.statements` one line at a time, as `check-library` does, with `parse-line` and `admit`. For a define line whose bodies call its functions (`calls-list-p`), it enters the names in the world, as `admit-define` does for a statement of a book, and calls `measure-entry` there.
- **A book.** It admits the library with `check-library`, and then reads and admits the book's statements as the checker's `run` does, with `parse-line` and `admit`. A define line with obligations leaves a pending entry; the tool calls `measure-entry` on it, in the world in which the checker would read its entry, and then `finish`, as a skip entry does. Every other pending entry is finished in the same way.

`measure-entry` (`checker/check.lisp`) is what the checker does when it reads a line `(measure F M1 ... Mk)` of the proofs: it checks that `F` is the first function of the definition and that each `Mi` is a term over the formals of the `i`-th function whose functions are in use, and computes the obligations with `termination-obligations` (`checker/admit.lisp`), or refuses the entry when their sizes pass the budget. The clauses it gives are those that the checker asks a proof of.

**The measure entry.** For a define line whose first function is `F`, the entry is `(measure F1 M1 ... Mk)`, where `F1`, ..., `Fk` are ACL2's property `recursivep` of `F`, in its order, and `Mi` is the measure of the justification that ACL2 stores for `Fi`. It is printed with `bm-line` of `checks/canon.lisp`, the one printer of the formats, and read with the checker's reader in the world of the define line.

## ACL2's side

ACL2's measure conjectures for a definition are the clauses of its function `termination-theorem-clauses` (ACL2's source file `history-management.lisp`), called with the arguments that ACL2's function `termination-theorem` gives it: the names of the property `recursivep`; their formals; their stored bodies, `unnormalized-body`; the measures, the domain `mp` and the relation `rel` of their justifications (`measure-alist?`); their ruler-extenders (`ruler-extenders-lst`); and the property `loop$-recursion`. It builds ACL2's termination machine for each body (`termination-machines`, in `induct.lisp`) and the clauses from it (`measure-clauses-for-clique`). These clauses are the termination theorem that ACL2's lemma instance `:termination-theorem` states. When ACL2 admits a definition, it proves the same clauses, after its prover cleans them up (`clean-up-clause-set`, which removes subsumed and built-in clauses); that clean-up is part of proving them, and the comparison takes the clauses before it.

The clauses are printed with `bm-line`, as lines `(clause L1 ... Ln)`, and read with the checker's reader in the world of the define line, so that both sides are in the reader's form: the symbol whose text is `P::N` is the symbol of the package `BOYMOO` named by that text, and `COMMON-LISP::NIL` and `COMMON-LISP::T` are `NIL` and `T` (`export/README.md`, "What the proofs rest on").

## The comparison

Each definition gets one class, the fifth word of its line in `build/termination/`.

**`agree`: exactly.** The two lists of clauses, in the reader's form, are equal.

**`agree-tidy`: in normal form.** `spec/logic.md`, section 6, says that ACL2 writes its conjectures in a tidier form than the obligations: it strips from a test the functions that only carry guards, drops a test that a later one implies, folds a call of a primitive on constants, and negates by removing a `not` where it can; and ACL2 Core does none of them. So when the two lists are not equal, both are put in one normal form, by the same functions applied the same way to each side, and compared again. The checker's clauses are first written with ACL2's symbols: each symbol is found by its text among the symbols of ACL2's bodies, measures and conjectures for the definition; one not found would make the two sides differ. Then:

1. **Each literal**, with `X'` standing for `(sublis-var nil (remove-guard-holders-weak X nil))`: a literal `(not S)` becomes `(dumb-negate-lit S')`, and any other literal `L` becomes `(dumb-negate-lit (dumb-negate-lit L'))`. These are the functions by which ACL2's termination machine writes a test (`termination-machine-rec`): `remove-guard-holders-weak` removes `return-last`, `mv-list`, `the-check` and the other guard holders, `sublis-var` folds a call of a primitive on constants, as it does when ACL2 substitutes into a test, and `dumb-negate-lit` negates by removing a `not`, or by taking `X` for `(equal X 'nil)`.
2. **Each clause**: a literal `'NIL` is removed; a clause with a literal `'T` is removed; and a literal is removed when a later one implies it. ACL2 does the last when it adds a test that equates a term `Y` to a constant `C`, by `equal`, `eq`, `eql` or `=`: it removes each earlier test that says that `Y` is not another constant (`add-test-smart` and `simplify-tests`, in `induct.lisp`). In a clause, whose literals are the negations of the tests, that removes an earlier literal that says `Y` is `C2` when a later one says `Y` is not `C`, with `C` and `C2` different. A literal says that `Y` is `C` when it is `(E Y 'C)` or `(E 'C Y)`, `E` among those four, or `(not Y)` with `C` being `NIL`; it says that `Y` is not `C` when it is `(not (E Y 'C))` or `(not (E 'C Y))`, or `Y` itself with `C` being `NIL`.
3. **The list**: the clauses of one literal that is a call of `o-p` stand first, in their order, and a clause that repeats an earlier one is removed. The specification puts the clauses `((o-p Mi))` of all the functions first; ACL2 puts each before the clauses of the calls in that function's body.

Each step keeps the meaning of a clause. Step 1 replaces a literal by one equal to it as a proposition: a guard holder returns its last argument, a folded call has the value it is folded to, and `(not (not X))` and `X`, or `(not (equal X 'nil))` and `X`, are true together. In step 2, a literal `'NIL` is false, a clause with a literal `'T` is true, and a literal removed there is false whenever the later literal is false: if `Y` is `C`, then `Y` is not `C2`. Step 3 changes only the order and removes copies. So a definition that agrees in normal form has obligations each of which is equivalent, as a proposition, to ACL2's conjecture in the same place, apart from clauses that are true by their form. The line of such a definition names the steps that changed each side, for example `checker=implied-test,negation acl2=o-p-first`.

**`agree-repeats`: in normal form, but for ACL2's removal of repeats.** The specification leaves out a clause that is the same as an earlier one. ACL2 leaves out one that is the same as a later one, up to the order of the arguments of `equal` (`conjoin-clause-to-clause-set`, in `simplify.lisp`, which `measure-clauses-for-fn` and `measure-clauses-for-clique` use to join the clauses). When a clause occurs twice with another between, the two lists have the same clauses in another order. For a definition that does not agree in normal form, the comparison builds ACL2's clauses again before that removal, with the functions that `measure-clauses-for-fn` uses on the same termination machines: for each function in order, the clause `(add-literal (MP M) nil t)` of its measure `M` and then `measure-clause-for-branch` of each call; it puts that list in normal form, which removes repeats as the specification does, and requires it to be the checker's.

**`agree-order` and `differ`.** Two lists in normal form that have the same clauses in another order, for a reason other than repeats, or that have different clauses. Either is a difference, and fails the command.

## What is not compared

Nothing is left out silently. Each of these is counted by its reason, and none fails the command:

- **`relation`: another relation** (`EDGE-CASES.md`, entry 6.4). A definition that ACL2 measured with a relation other than `o<` has conjectures `(mp m)` and `(rel m' m)`, while the obligations are stated with `o<` and are met by the embedded measure `(fn m)` (`spec/logic.md`, section 6). The checker is given ACL2's measure all the same, and the line says `calls-agree` when its clauses for the calls are ACL2's in normal form once ACL2's last literal `(rel A B)` is read as `(o< A B)` and its clause `((mp M))` as `((o-p M))`.
- **`measure-unknown`: a measure of the form `(:? v1 ... vk)`.** ACL2 stores such a measure for a definition that it admitted without proving its termination, and has no termination theorem for it (`termination-theorem` says so).
- **`loop$`: recursion in the quoted lambda of a `loop$`** (`EDGE-CASES.md`, entry 6.14). ACL2 measures calls that ACL2 Core treats as part of a constant, so the define line has no obligations, and the function is listed as `uncovered ... loop$`.
- **`subversive`: a recursion whose equation joins a constraint** (`EDGE-CASES.md`, entry 6.6). When a test or an argument of a call mentions a function constrained by the encapsulate around it, ACL2 holds the definition as subversive and puts its equation in the constraint; there is no define line, and the function is listed as `uncovered ... subversive`.
- **`refused`: a measure entry that the checker refuses**: a measure that calls a function not in use when the define line is read, or obligations whose sizes pass the budget. The line gives the checker's reason.

The other entries of `EDGE-CASES.md` on definitions are compared, not set aside. A body is the stored, unnormalized body on both sides (entry 6.5). A measure that ACL2 guessed is compared like one that the definition declared (entry 6.3). The ruler-extenders are those ACL2 stored, and the executable half of an `mbe` is walked by neither side (entry 6.2): the comparison is the test of that entry over every definition.

## Every function is accounted for

Each run collects the functions with a justification that the book adds to ACL2's world; for the library, all of those in the world ACL2 starts with. Each must be a function of a definition compared, or listed as `uncovered` with a reason above. A function with a justification whose define line has no obligations, for no reason above, and a define line with obligations whose first function has no justification (`no-justification`), are differences, and fail the command.

## The measures of the aids

For each book, the command also checks that the prover's aids that the exporter wrote, the lines `(measure F M REL HOW)`, give each function the measure and relation of its justification in ACL2's world, and the other way round.

## The cases

`cases.lisp` holds a definition of each class but `differ` and `agree-order`, for which there is no example, and `cases.txt` the class each must have:

| Definition | Class | Why |
|---|---|---|
| `bm-repeat` | `agree-repeats` | With the ruler-extenders `:all`, the call `(bm-repeat (cdr x))` is recorded twice under the same tests, with `(bm-repeat (cddr x))` between. |
| `bm-implied` | `agree-tidy` | The test `(eq (car x) 'b)` implies the earlier `(not (eq (car x) 'a))`, which ACL2 drops. |
| `bm-even`, `bm-odd` | `agree-tidy` | Two functions with one measure: ACL2 puts `(o-p M)` between the clauses of the two bodies. |
| `bm-w` | `relation` | Measured with a relation of the book's own, as in `checks/facts.lsp`. |
| `bm-l1` | `uncovered loop$` | Recursion in a `loop$`, as in `checks/facts.lsp`. |
| `bm-sub` | `uncovered subversive` | Its call is on `(bm-step x)`, a function of the constraint of the encapsulate around it. |
| `bm-inside` | `refused` | Its measure `(bm-size x)` calls a function of the constraint of the encapsulate around it; since no test or argument of a call does, ACL2 does not hold it as subversive (its function `subversivep` does not look at the measure). Its body calls no function of the constraint, so its define line stands before the constrain line (`export/README.md`, section 5 of `core.lisp`), and the measure calls a function not yet in use. |
| `bm-outside` | `agree` | The same definition after the encapsulate, where `bm-size` is in use. |

## The result

`sh review/termination/run.sh`, run on 2026-11-24 in 231 seconds with ACL2 8.7, printed the lines of `build/termination/summary.txt`; these are its counts. A definition is one define line with obligations; it has one or more functions. A book's statements hold those of the books it includes, so a definition is counted in every book whose statements hold it; the last row counts each distinct define line once.

| Set | Definitions | Functions | Exactly | In normal form | In normal form but for ACL2's removal of repeats | Differ | Another relation | Measure `(:? ...)` |
|---|---|---|---|---|---|---|---|---|
| The ground theory | 14 | 14 | 11 | 3 | 0 | 0 | 0 | 0 |
| The library | 451 | 509 | 330 | 118 | 0 | 0 | 1 | 2 |
| The 460 books | 9,886 | 10,450 | 8,008 | 1,858 | 3 | 0 | 5 | 12 |
| The books, each define line once | 1,164 | 1,228 | 932 | 223 | 3 | 0 | 3 | 3 |

- **Every function is accounted for.** The 523 functions with a justification in the world ACL2 starts with are the 14 of the ground theory and the 509 of the library's definitions, and the 10,450 that the books add are those of their definitions. No define line with obligations lacks a justification, and no function with a justification lacks a define line with obligations. No book has a recursion in a `loop$` or a subversive recursion, and the checker refused no measure entry.
- **The clauses.** The checker computed 34 clauses for the ground theory, 1,372 for the library, 25,631 over the books and 2,999 for the distinct define lines of the books.
- **The aids.** For every book, the measures and relations of the aids are those of ACL2's world.
- **The cases.** The eight definitions of `cases.lisp` have the classes that `cases.txt` gives.
- **The steps of the normal form.** Over the 347 definitions that agree in normal form, counting those of the ground theory, of the library and each distinct define line of the books once, the steps that changed the checker's clauses were `guard-holders` for 191 definitions, `implied-test` for 75, `negation` for 46 and `false-literal` for 2; those that changed ACL2's were `o-p-first` for 91, `guard-holders` for 41, `repeat` for 3 and `false-literal` for 2. The folding of constants never changed a literal that `remove-guard-holders-weak` left unchanged, and no clause was removed for a literal `'T`. ACL2's clauses needed `guard-holders` where a substitution for the formals of a lambda brought a guard holder into a test, since ACL2 removes guard holders from a test before it substitutes: in `string-prefixp-1` of the library, for example, the actual `((lambda (var) (the-check (signed-byte-p '61 var) '(signed-byte 61) var)) ...)` of a `let` stands in ACL2's test `(not (eql (char str1 ...) ...))`.

## What the comparison found

**No difference.** For every definition that could be compared, the checker's obligations are ACL2's measure conjectures, clause for clause and in order, up to the tidying that `spec/logic.md`, section 6, says ACL2 does and ACL2 Core does not, and up to the two matters of order below. No `differ` and no `agree-order` occurred.

**The order is the specification's, not ACL2's, in two ways.** `spec/logic.md`, section 6, says the obligations "are ACL2's measure conjectures" and gives their order. As sets they are; in order they differ from ACL2's in two ways, both stated by the specification and both followed by the checker:

- For a definition of several functions, the specification puts the clauses `((o-p Mi))` of all the functions first; ACL2 puts each before the clauses of the calls in that function's body. This changed ACL2's clauses for 91 of the definitions that agree in normal form, among them 39 of the 40 definitions of the library that have two functions or more.
- When a clause occurs twice, the specification keeps the first copy and ACL2 the last, comparing up to the order of the arguments of `equal`. Three definitions of the books show it: `STD::MY-FLATTEN-TERM`, `STD::MY-FLATTEN-TERM2` and `STD::DOC-TEST` of `std/util/tests/defines`, each a definition of two functions in which the clause of the call in the first body comes again from the second body, after the clause of another call. The smallest example is `bm-repeat` of `cases.lisp`: the checker's clauses are `(o-p M)`, then the clause of `(bm-repeat (cdr x))`, then that of `(bm-repeat (cddr x))`; ACL2's have the last two the other way round.

A proof gives the proofs of the obligations in the specification's order, so a tool that writes the proofs from ACL2's termination theorem must put its clauses in that order.

**A measure that calls a constrained function, inside an `encapsulate`.** ACL2 holds a recursion as subversive, and joins its equation to the constraint, only when a test or an argument of a call mentions a function of the constraint; its function `subversivep` does not look at the measure. So `bm-inside` of `cases.lisp`, whose measure calls the constrained `bm-size` but whose body does not, is a definition of its own. The exporter places its define line before the constraint, since its body calls no function of the constraint (`export/README.md`, section 5 of `core.lisp`); there the checker refuses ACL2's measure, which calls a function not yet in use. A proof of such a definition needs a measure whose functions are in use at its define line, as `(acl2-count x)` serves for `bm-inside`. No definition of the library or of the 460 books is of this kind.

**Measures that ACL2 does not hold.** Besides `genvar1` and the four functions of `apply$`, which ACL2 admits in its own start without a proof of termination, the book `projects/numbers/euclid` declares `dm::least-divisor`, `dm::gcd-nat` and the two functions of `dm::r-nat` with `:measure (:? ...)` and proves them in a book that it includes locally, `projects/numbers/support/euclid`; including the first, ACL2 stores the `(:? ...)` measures and has no termination theorem. Four books hold these three definitions. A proof of them takes its measure from elsewhere, for example from the definitions of `projects/numbers/support/euclid`, which the comparison finds to agree.

**Other relations.** `do$` of the library and `bx-lex` of `build/choice` are measured with `l<`, and `power2p` and `power2-syntaxp` of `rtl/rel9/arithmetic` with `e0-ord-<`. For each, the checker's clauses for the calls are ACL2's in normal form once ACL2's relation is read as `o<`.
