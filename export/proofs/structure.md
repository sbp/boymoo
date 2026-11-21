# Completeness and order of the exporter

Run `sh export/proofs/structure.sh` from the repository root with ACL2 8.7.
The script certifies the proof books and reloads their certificates with
skipped proofs, added axioms and trust tags disallowed. It also checks
the hypotheses on ACL2 worlds and runs the examples described here.

## Shared constraint roots

Two nested signed encapsulates can share one constraint in an
admitted ACL2 world. ACL2 records their formulas under the same
function, the constraint root. The `nested-constraint-name-reuse`
test has one closing record whose signature starts with
`STRUCTURE-NESTED-G` and another whose signature starts with
`STRUCTURE-NESTED-F`. Both name an unnamed corollary
`|STRUCTURE-NESTED-F constraint 2|` on distinct lines. The model
counts two eligible records and both exports report the conflict by
name. [Executable counterexample](structure-generated-tests.lsp)

## Event names and effective introductions

A record is the value of `global-value` at an `event-landmark`. The
range contains the records with event numbers `lo < number <= hi`.
For the library, `lo` is zero. The name is an element of the record's
decoded `namex`, with a single symbol or string treated as one name.
An empty list and the numeral zero stand for no names. The `defconst`
record for `NIL` names that symbol. The definitions use ACL2's event tuple
convention in `make-event-tuple` and `access-event-tuple-namex`.

A supplying statement uses the name in a position that introduces it
in `spec/formats.md` and `spec/logic.md`.
A `constrain` introduces the names of its functions and formulas.
A package has a string identifier, introduced by its first declaration.
Opening a hidden package with the same imports introduces the symbol
for its rule. The package identifier is already available.

The count skips byte-for-byte repeats across the library and book.
Sections 1, 2 and 7 of the format specify a unique canonical text for
each line datum, so the model uses equality of line data. One statement
counts once for a name even if the name occurs more than once in the
statement. The order model checks for such repeats within a statement
and for collisions between distinct statements. A repeat of a library
line in a book contributes zero new introductions.

The following names are outside the obligation to write a statement.

- A definition whose event is in program mode, and a program-mode
  function of a single-threaded object, can have program text. A
  promotion to logic mode has its own defining record.
- An `include-book` record names a file. The included name-bearing
  events have their own records.
- An event outside the statement kinds owes no statement for a name
  without a logic function, theorem or reserved-name property. A
  reserved name requires a statement or a diagnostic.
- The library may rely on the ground theory for its five packages,
  the constants `T` and `NIL`, the supplied ground definitions, and
  the fixed 84 axiom names in `spec/ground.txt`.
  Other axioms are subject to the usual coverage claim.

## Completeness theorems

The range and record hypotheses are
`structure-range-recordsp`, `structure-range-namep` and
`structure-namex-shapep`. The landmark numbers must be integers in
strictly decreasing order in the world and selected depths must be
integers. The record and name must be in the selected range, and
the shape of `namex` must match the event kind where the proof
interprets its fields. A matching library has the same line data as
the library reconstructed from the startup range in the book world.

- **`structure-library-lines-complete-or-note`.** Under the range
  and record hypotheses, every name due from `bx-library-lines` beyond
  those supplied by the ground theory has exactly one effective
  introduction or a note naming it.
- **`structure-book-lines-complete-or-note`.** Under the range and
  record hypotheses and with a matching library, every name due from
  `bx-book-lines` has exactly one effective introduction across the
  library and book or a book note naming it.

The alternatives can overlap. A second, distinct statement that takes
the same symbol gets a note listing that symbol as already in use.
A conflict in a book's library is carried in a nested library note
with the original diagnostic data. The count describes the supplied
statement sequence, including when a checker would stop at a prior
failure.

`structure-library-lines-supply-or-note` and
`structure-book-lines-supply-or-note` give the existence claim directly
for the respective entries. Both assume an in-range name of the
required shape that is due a statement. The library also assumes
that the ground theory does not supply that name. Each returns a
supplying statement or a conversion note for the name. The separate
`structure-library-lines-report-second-introduction` and
`structure-book-lines-report-second-introduction` theorems give the
named conflict for more than one effective introduction. The book
version assumes a matching library and counts across both files.

If any formula of a constraint has no available name, the exporter
returns a note listing the constraint's functions followed by every
formula name that is available. The `constraint-name-exhaustion` test
admits an encapsulate with a named theorem and a constrained helper
definition whose equation takes a generated name. Labels occupy all
1,001 possible names of the equation. Both entries omit the constraint
and the note names the theorem and both functions.
[Exhaustion test](structure-exhaustion.lsp)

`structure-walk-library-fuel-suffices` proves that the fuel supplied
to the library walk suffices for every candidate list. The accounting
charges the remaining roots, unused dependencies and outstanding stack
frames. `structure-library-order-keeps-line` then retains each
candidate statement of a recognized kind through the walk, including
when a cycle causes a diagnostic. The library completeness theorem
uses this bound without a fuel hypothesis.

## Generated formula names

A generated constraint formula name belongs to the package of the
function that supplies its stem. The suffix is `definition`, `choice`
or `constraint` and a position. It can have an additional decimal
number to distinguish an occupied spelling. The proof reads the
spelling from the right to recover the stem, including any spaces or
digits that belong to the function's own name.

`structure-fresh-name-excludes-registered-symbols` proves that a
successful search returns a non-keyword of the same package as the
source symbol and avoids the registered function, theorem and
reserved names in the world. Two functions in different packages
therefore cannot acquire the same generated symbol from a shared
import. The `shared-import-formula-names` test declares two packages
that both import `ACL2::|F constraint 1|`. Their constraints use
`|F constraint 1 1|` in their respective packages.

The model counts the event records that could supply a name.
An explicit record name or package rule can supply its symbol.
A closing encapsulate record can supply its signature and siblings,
and it can generate a formula name whose stem belongs to its root
or a sibling. The bound counts distinct records sharing a root
separately.

- **`structure-library-lines-generated-name-bound`.** When the
  range has the required numbers, depths and record shapes, a
  non-nil unregistered symbol has at most as many effective
  introductions in the library as records that could supply it.
- **`structure-book-output-generated-name-bound`.** Under the
  corresponding conditions on the book's range, a non-nil
  unregistered symbol has the same bound on its introductions in
  the book's statements alone.
- **`structure-book-lines-generated-name-bound`.** Under the
  same conditions on both ranges and with a matching library,
  a non-nil unregistered symbol has at most as many effective
  introductions across the two files as the sum of the two record
  counts.

Thus a generated formula name with at most one eligible record
has at most one effective introduction. The bound counts distinct
lines that supply the name. Releasing an already created line from
an encapsulate bundle cannot add a distinct line to the count.

## Order theorems

The order definition uses the function signatures, occupied names and
package declarations in the prefix. It checks each call and its arity,
including lambda bodies and actuals and executable halves of `mbe`.
Quoted data contribute symbols,
and their contents contribute no calls. A `define` or `constrain` has
its own signatures in scope for checking its terms. A `choose` body
uses the preceding signatures. Every symbol requires a preceding
declaration of its package and a spelling that the package does not
import. Each new symbol must be fresh in the prefix and distinct on its
line. An open package can follow a hidden declaration of that package
with exactly the same imports. The ground theory supplies initial
declarations without adding earlier input lines for the repeat rule.
[Order definition](structure-spec.lisp)

- **`structure-library-lines-order-or-note`.** Given the ground
  inventories, `bx-library-lines` returns statements in order or
  returns an order note.
- **`structure-book-lines-order-or-note`.** Given the ground
  inventories and a matching library, `bx-book-lines` returns statements
  whose combined library and book sequence is in order or returns an
  order note covering the library or the book.

`structure-ground-contextp` relates the explicit inventories to
the ground primitives, supplied ground definitions, ground axiom names
and package declarations. It gets the function arities and package
imports from the ACL2 world. `structure-check-statements-order`
relates the independent model to section 8 of the core. The diagnostic
scan produces one order note per failing first occurrence and
constructs the prefix inventories predicted by the model.
`structure-library-notes-count-order-failures` and
`structure-book-notes-count-order-failures` bound the number of model
failures by the returned order-note count under the same hypotheses as
the respective order theorems. The book count includes the failures
carried inside the library note.

The exporter returns the lines along with any diagnostic. Its scan can
install declarations from a failing statement and continue. A checker
stops at the first failure. Dependent items within an encapsulate can
follow its constraint, including chains of items that call one another
in event order. If the resulting order has a dependency failure, it
falls under the same order-note claim.

## Hypothesis tests

| Predicate | How the script checks it |
|---|---|
| `structure-range-recordsp` | `startup-world` checks decreasing event numbers and integer depths in the bare startup world. Each specimen test checks the world saved immediately after the specimen is included, using its saved upper event number. |
| `structure-range-namep` | The tests select the range by an independent full traversal of the landmarks and enumerate the decoded names of its records. |
| `structure-namex-shapep` | The startup and specimen tests check the required `namex` shapes of every selected record. |
| `structure-ground-contextp` | The script projects signatures, symbol facts and package imports from `spec/ground.txt`. It checks the arities and imports against the startup and specimen worlds and compares the ground names with the projected names. |
| `structure-library-prefix-matches-p` | Each specimen compares the library reconstructed from its world with the actual statements saved from the startup library export. |
| `structure-naming-recordsp` | The library and specimen tests check the required shapes of every record in the ranges supplying either file. |
| `structure-unregistered-symbol-p` | The generated-name checks inspect the world properties of each output formula name. For a name absent from the function, theorem and reserved-name inventories, the tests check that the independent spelling model identifies its stem and that exactly one record could supply it. |

The script checks the library and each combined input with the independent
order model, then checks each event name for coverage. It includes
`std/lists/append`, `misc/defpun`, `std/stobjs/absstobjs`,
`misc/hidden-defpkg-checks/top` and `ordinals/e0-ordinal` from
`export/books.txt`, each separately and all five in `combined-books`.

The focused tests supply property-list worlds and statement sequences
for an order note on a self-calling choice, an order note on an imported
spelling, a library failure
carried through to a book, a named conflict carried through that
library note, named notes for unsupported reservations and unlisted
constrained functions, retention of a non-ground axiom, and order
within a chain of items held after a constraint. It also exercises
exact repeats, repeats across a file boundary, a conversion note,
and opening a hidden package. The `constraint-name-exhaustion` test
checks named coverage when the available names for a formula are exhausted.
[Focused tests](structure-tests.lsp)

The subject of the theorems is the returned statement and note data.
Full statement syntax, the rules for eligible names beyond freshness,
obligation proofs, proof-file declarations, validity of world
metadata, guards, faithfulness of bodies and formulas, program and
aids data, and file I/O are separate properties.

## Verification

On 2026-11-21, `sh export/proofs/structure.sh` under ACL2 8.7 printed
`all structure checks passed`. The strict certificate reload, the
startup and library checks, the five specimens separately and together,
and all focused tests passed. The run, including certification of the
core and printer, took 44.86 seconds elapsed.

The proof books occupy 231,948 bytes, measured on the same date with
`wc -l -c export/proofs/structure-*.lisp`. The table shows the
certification times that ACL2 reported for those books.

| Proof book | Lines | Seconds |
|---|---:|---:|
| `structure-spec.lisp` | 274 | 0.07 |
| `structure-events.lisp` | 205 | 0.90 |
| `structure-enclosure.lisp` | 126 | 0.73 |
| `structure-walk.lisp` | 182 | 0.47 |
| `structure-items.lisp` | 275 | 0.66 |
| `structure-held-items.lisp` | 345 | 0.29 |
| `structure-order.lisp` | 339 | 0.67 |
| `structure-counts.lisp` | 266 | 0.97 |
| `structure-coverage.lisp` | 489 | 0.45 |
| `structure-ground-filter.lisp` | 100 | 4.69 |
| `structure-entry-order.lisp` | 300 | 0.33 |
| `structure-entry-coverage.lisp` | 327 | 0.81 |
| `structure-name-spelling.lisp` | 290 | 1.21 |
| `structure-name-routing.lisp` | 547 | 1.42 |
| `structure-generated-names.lisp` | 532 | 7.89 |
| **Total** | **4,597** | **21.56** |
