# Faithfulness of the exporter

Run `sh export/proofs/faithful.sh` from the repository root with ACL2
8.7. The command certifies the proof books in `build/export/acl2/`
and checks their certificate annotations for skipped proofs, axioms
and trust tags. It also runs the world tests, outcome tests and
counterexamples in `export/proofs/faithful-tests.lsp`,
`export/proofs/faithful-outcome-tests.lsp` and
`export/proofs/faithful-counterexamples.lsp`.

The proofs concern the data returned by `bx-library-lines` and
`bx-book-lines`. The predicates read ACL2's properties directly
and specify the transformations of those properties. For every
returned statement, the proof traces its data to the event that
produced it. This includes items released by an encapsulate and
library statements that have been reordered.

## Statement data

Each theorem in this table assumes that the line has the indicated
word and is in the first result of either entry function. The table
lists any additional hypotheses.

| Theorem | Claim and additional hypotheses |
|---|---|
| `faithful-define-statement` | With `plist-worldp-with-formals`, a `define` line carries every listed function's stored formals and unnormalized body and the first function's stored ruler-extenders. |
| `faithful-define-ruler-extender-exception` | With `plist-worldp-with-formals` and a definition listed in the `define` line, the shared ruler-extenders match that definition's exactly when they agree with the first function's stored ruler-extenders. |
| `faithful-theorem-statement` | A `theorem` line carries the ACL2 `theorem` property of its name. |
| `faithful-axiom-statement` | An `axiom` line carries the ACL2 `theorem` property of its name. |
| `faithful-fact-statement-has-world-record` | With `faithful-fact-world-p`, a `theorem` or `axiom` line has a formula present in its name's ACL2 `theorem` property. |
| `faithful-package-statement` | With `faithful-package-world-p`, a `package` line gives the recorded imports of an open package and agrees with its imports axiom. For `COMMON-LISP` the known package table suffices. |
| `faithful-hidden-package-statement` | With `faithful-known-packages-p`, a `hidden-package` line gives the recorded imports of a package that ACL2 holds hidden or whose hidden declaration is in a world landmark. |
| `faithful-choose-statement` | With `plist-worldp-with-formals`, a `choose` line gives its name's stored formals and reconstructs its stored choice axiom as specified below. |
| `faithful-constrain-statement` | With `plist-worldp-with-formals` and `faithful-constraint-world-p`, a `constrain` line lists exactly the recorded sibling functions with their stored arities, gives each formula a name and covers all and only the stored conjuncts when ACL2 records a constraint. |
| `faithful-constrain-formula-source` | With `plist-worldp-with-formals`, `faithful-constraint-world-p`, `faithful-fact-world-p` and a formula pair in the `constrain` line, the formula and its label have one of the sources described below. |
| `faithful-constrain-name-in-use` | With the hypotheses of `faithful-constrain-formula-source` and a formula name in use in ACL2's world, the pair gives the formula in the `theorem` property of that very name. |
| `faithful-reserve-statement` | A `reserve` line names a macro, constant, label, theory, single-threaded object or live object variable in ACL2's world. |

A definition body is ACL2's `unnormalized-body`, including translated
`return-last` applications. The ruler-extenders come from its
`justification` record and are `nil` when that record is absent.
The definition and fact equalities use `nil` as the default for
property lookups. The fact record theorem guarantees presence under
its world hypothesis. The data tests check the presence of formals,
bodies and fact formulas for the lines they exercise. The library
omits axioms whose names are in the ground theory.

For choice, `faithful-choice-axiom` builds the literal of
`spec/logic.md`, section 6, with ACL2's `subcor-var` for substitution.
`faithful-beta-normal-form` substitutes the reduced actuals of each
translated lambda application for its formals and preserves quoted
data. With this transformation, the recorded `defchoose-axiom`
equals the literal of the line. When both free-variable lists are
empty, it can instead equal the exact strengthened literal built
with the same nullary call on both sides of the equality. The
extra conjunct is then true by reflexivity.

For a recorded constraint, `faithful-matching-conjuncts` first
splits a formula with ACL2's `flatten-ands-in-lit`. If those
conjuncts are not all in the constraint, it splits after applying
`remove-guard-holders-weak` with its lamp set to `t`. Each written
formula must match by one of these tests, and every stored conjunct
must occur in the matched results. The written formula itself
is preserved. The weak routine leaves quoted lambda objects alone.
The theorem compares sets of conjuncts, so their order and
multiplicity are immaterial.

A constraint formula under a named fact gives its stored `theorem`
property and mentions a sibling of the constraint. A generated label
identifies a sibling's stored `defchoose-axiom`, a sibling's defining
equation, or the conjunct at the indicated position in the stored list.
The defining equation of a recorded constraint is its first conjunct
that equates a call of the function on its stored formals with a body.

When ACL2 marks a constraint unknown, the sibling, arity and formula
source claims still apply. A definition label in that case identifies
the equation formed from the sibling's recorded formals and
unnormalized body. The formulas are the selected known facts, choice
axioms and equations. Coverage of a recorded list applies only when
ACL2 has one.

## Generated constraint labels

The anchor of a generated label is the sibling function for a choice
or defining equation and the constraint owner for a conjunct named by
position. A generated label belongs to its anchor's package, is a
non-keyword symbol and has none of the ACL2 properties that put a name
in use. Its spelling ends with the purpose word, the position for an
indexed conjunct and an optional decimal suffix from 1 through 1,000.
The exporter passes over imports when it interns the spelling.

`faithful-label-anchor` and `faithful-label-key` read the purpose and
decimal components from the right so that spaces in the anchor's name
are preserved. `faithful-world-formula-for-generated-label` uses the
decoded symbol and purpose to read the stored choice axiom, defining
equation or indexed conjunct. The source theorem's hypotheses are
`plist-worldp-with-formals`, `faithful-constraint-world-p` and
`faithful-fact-world-p`, together with a formula pair in a returned
`constrain` line.

| Theorem | Claim and hypotheses |
|---|---|
| `faithful-generated-constraint-label-identifies-world-formula` | With the source hypotheses and a label unused in ACL2's world, the label decodes to the owner and exact formula of the pair. Its spelling also rules out names ending with the package rule's suffix. |
| `faithful-shared-generated-label-has-one-formula-and-owner` | With the source hypotheses for both pairs, a shared generated label denotes the same stored formula and constraint owner in both returned lines. |
| `faithful-generated-name-introductions-stay-with-owner` | With the source hypotheses, `faithful-function-event-world-p`, a generated label and another returned line introducing it, the other line is a `constrain` that gives the same formula and constraint owner. |

The last theorem counts function names, fact names, reservations,
package rules and constraint formula labels as introductions. A line
can mention a symbol in its data without introducing it. The theorem
applies to lines from either entry in any order.

## Constraint outcomes

| Theorem | Claim and hypotheses |
|---|---|
| `faithful-book-constraint-statement-or-note` | With `plist-worldp-with-formals` and `faithful-constraint-world-p`, each selected encapsulate event with a signature gives a faithful constraint statement or a missing-label note in `bx-book-lines`. |
| `faithful-library-constraint-statement-or-note` | Under the same world and signed-event conditions in the library range, `bx-library-lines` gives the faithful constraint statement, a missing-label note or an incomplete-library-order note. |
| `faithful-book-exhausted-constraint-names-noted` | Under the book outcome hypotheses, when a selected formula lacks a label, a returned missing-label note names every sibling function and every formula with an available label. |
| `faithful-library-exhausted-constraint-names-noted` | Under the library outcome hypotheses, when a selected formula lacks a label, a returned missing-label note names every sibling function and every formula with an available label. |

The event hypothesis in each outcome theorem is membership in the
entry's event range, type `encapsulate` in the ACL2 event tuple and
a nonempty signature. The result is identified by the constraint
owner obtained through ACL2's `constraint-info`. The auxiliary
theorem `faithful-constraint-naming-outcome` specifies the two
outcomes of formula naming. A missing name on a selected formula
gives the note `constraint with a formula for which no unused name
was found` with exactly the functions of the constraint followed
by every non-`nil` label on its selected formulas. When every
formula has a name, the naming result is the constraint statement.

The event walk can hold back statements that use a constraint's
functions or the functions of previously deferred statements. The
proof establishes that a deferred item has a later releasing
event, including when a release places an item in an outer
encapsulate's bucket. It also distinguishes a constraint's formula
candidates from deferred lines. A cycle diagnostic does not
substitute for a library statement. The incomplete-order note
accounts for exhaustion of the library walk's fuel, whose
sufficiency is outside these theorems.

## Runner program text

These theorems assume membership in the second result of the indicated
entry function and the corresponding line word.

| Theorem | Claim and additional hypotheses |
|---|---|
| `faithful-library-program-define` | With `plist-worldp-with-formals`, `faithful-stobj-program-world-p` and `faithful-nonprogram-fns-p` for the ground functions, each program definition gives the recorded formals and the body specified below. |
| `faithful-book-program-define` | With `plist-worldp-with-formals` and `faithful-stobj-program-world-p`, each program definition gives the recorded formals and the body specified below. |
| `faithful-attach-program-line` | An `attach` line gives the pair found in ACL2's `attachment` property, by reading its alist or following its reference to a function holding the alist. |

A logic-mode body is the recorded unnormalized body. A program-mode
body comes from that property when present and otherwise from a
successful translation supplied to the entry function.
`faithful-executable-half` replaces a translated `mbe` application
with its executable argument, recursively through applications and
lambda bodies. Program ruler-extenders, the shell's translation and
the selection of new attachments relative to startup are outside
these theorems.

## Hypotheses and tests

| World hypothesis | Condition checked on each sampled world |
|---|---|
| `plist-worldp-with-formals` | The world has the ACL2 property-list shape and each `formals` binding is a true list or is marked unbound. |
| `faithful-known-packages-p` | ACL2's `known-package-alist` global is present. |
| `faithful-package-world-p` | The known package table is present and its open entries agree with their imports axioms, with `COMMON-LISP` allowed to have no matching axiom. |
| `faithful-constraint-world-p` | Each encapsulate landmark has no signature or a list of signature functions in the recorded sibling set. The siblings have recorded formals and share the named constraint owner, which refers to itself. A recorded constraint is a list of individual conjuncts. |
| `faithful-fact-world-p` | Each named theorem, axiom and choice landmark has its formula in the corresponding property. |
| `faithful-function-event-world-p` | Each function listed by a `defun`, `defuns` or `defchoose` event landmark has a recorded `formals` property. |
| `faithful-stobj-program-world-p` | Each program-mode function with a formal list named by a `defstobj` or `defabsstobj` event has a stored unnormalized body. |
| `faithful-nonprogram-fns-p` | The ground functions supplied to `bx-library-lines` are outside program mode. The script reads their names from `spec/ground.txt`. |

The seven world tests check every listed hypothesis at startup,
after each of `misc/hidden-defpkg-checks/top`, `misc/defpun`,
`std/alists/alist-equiv`, `std/stobjs/absstobjs` and `misc/dft-ex`,
and after `misc/defattach-example` and the package, choice,
guard-holder and program-mode examples. They capture these worlds
before admitting proof and test functions.

The data tests check the statement and program lines in the startup
library range and the combined book range. The book test exercises
all eight statement words, and the library and book outcome tests
check every signed encapsulate in their ranges. The guard-holder
case exercises a named formula that covers two conjuncts and needs
the removal step for the match. The program tests exercise both
program words, a supplied translation for a startup function with
no stored body, and an `mbe` in a stored program body.

The outcome tests also check a strengthened choice without formals
with one and with two bound variables. The exhaustion tests in both
entries occupy all 1,001 spellings for a conjunct and check that the
note carries the function, the named theorem and the available
generated label for another conjunct. Two packages that import the
same unused symbol each use a label in their own package. The
keyword import example checks that a safe suffix
is used and that a chain of two definitions is released after its
constraint. A second ACL2 example checks a sibling's defining equation
inside its constraint and an independent definition outside the group.
A world built with explicit event landmarks exercises
the named notes for a constrained definition and a constrained
choice absent from the sibling list. The library axiom test checks
that an axiom outside the ground theory is present with its
recorded formula.

## Counterexamples and scope

- **Different ruler-extenders in one clique.** ACL2 admits
  `faithful-even` with `:all` and `faithful-odd` with `(cons)`.
  The single `define` line carries `:all`, and the notes name the
  clique. The format has one field for the entire group. The
  `different ruler-extenders` test checks this result.
- **A nested encapsulate can give two lines for one stored
  constraint.** The inner signature function depends on the outer
  one, and ACL2 records their constraint under the outer function.
  `bx-book-lines` returns two distinct `constrain` lines for that
  owner. Both use `|FAITHFUL-NESTED-OUTER constraint 2|` for the same
  conjunct. The `nested constraint shares a generated label` test
  checks the shared owner, label and formula, and the order
  diagnostic.

The data proofs concern the emitted lines. With the constraint
outcome theorems, they account for signed encapsulates in the
selected ranges. Completeness for other event kinds and the overall
admission order are outside their scope. The proofs also leave
format bytes, shell translation and ACL2's interpretation of its
recorded properties to their respective checks.

## Certification results

On 2026-11-21, `sh export/proofs/faithful.sh` with ACL2 8.7 ended
with `all faithfulness checks passed` in 377.36 seconds elapsed.
All 19 proof books passed the certificate audit and all 24 tests
passed. The eight world hypotheses returned true on all seven
worlds. On the data tests, the independent predicates agreed with
4,151 library statements, 394 book statements, 1,499 library
program lines and 158 book program lines.

The proof books total 6,001 lines and 286,599 bytes, measured with
`wc -l -c export/proofs/faithful*.lisp` on the same date. The last
column gives the certification time reported by ACL2 to the script.

| Book | Lines | Seconds |
|---|---:|---:|
| `faithful-origin` | 549 | 12.39 |
| `faithful-routing` | 593 | 0.74 |
| `faithful-kinds` | 205 | 0.32 |
| `faithful-definitions` | 290 | 0.29 |
| `faithful-world` | 147 | 0.18 |
| `faithful-packages` | 319 | 1.28 |
| `faithful-choice` | 254 | 0.36 |
| `faithful-conjuncts` | 234 | 0.85 |
| `faithful-constraints` | 546 | 1.08 |
| `faithful-candidates` | 320 | 0.39 |
| `faithful-constraint-names` | 361 | 0.31 |
| `faithful-constraint-outcomes` | 372 | 0.34 |
| `faithful-reserve` | 127 | 0.21 |
| `faithful-label-spelling` | 273 | 0.73 |
| `faithful-generated-names` | 528 | 2.49 |
| `faithful-program-data` | 191 | 0.23 |
| `faithful-program-items` | 232 | 0.67 |
| `faithful-program` | 294 | 0.31 |
| `faithful-attachments` | 166 | 0.20 |
| **Total** | **6,001** | **23.37** |
