# Well-formed exporter lines

The proofs cover the statement and program outputs of `bx-library-lines`
and `bx-book-lines`. A line is the pair `(WORD ARGS)` as ACL2 data.
`wf-statement-line-p` and `wf-program-line-p` recognize the data that
the format tables specify. The statement recognizer includes the
non-keyword name rule from the language and requires every formula
in a constraint to have a name. The recognizers use the grammar in
`well-formed-syntax.lisp` and ACL2's rules for translated terms and
legal variables. The specification is in `spec/formats.md` and
`spec/language.md`.

## Made-name reuse in nested constraints

Two distinct `constrain` lines from one export can introduce the same
made name. ACL2 associates both signatures in this example with the
constraint owned by `WF-OUTER`. Each line names the unnamed corollary
from that owner and its position, so each introduces
`|WF-OUTER constraint 1|`. The first line lists `WF-INNER` first and
the second lists `WF-OUTER` first. The notes include an order failure
whose `:NAME-IN-USE` entry names the shared symbol.

```lisp
(include-book "build/export/acl2/core")
(assign wf-nested-lo (max-absolute-event-number (w state)))
(encapsulate (((wf-outer *) => *))
  (local (defun wf-outer (x) x))
  (defthm wf-outer-law
    (equal (wf-outer x) x)
    :rule-classes ((:rewrite :corollary (equal (wf-outer x) x))
                   (:rewrite :corollary
                    (equal (wf-outer (cons x y)) (cons x y)))))
  (encapsulate (((wf-inner *) => *))
    (local (defun wf-inner (x) (wf-outer x)))
    (defthm wf-inner-law
      (equal (wf-inner x) (wf-outer x))
      :rule-classes nil)))
(set-guard-checking :none)
(value-triple
 (mv-let (statements program notes aids)
   (bx-book-lines nil 0 (@ wf-nested-lo)
                  (max-absolute-event-number (w state)) nil "" "" (w state))
   (declare (ignore program aids))
   (list statements (bx-words '("note") notes))))
```

Both lines satisfy the statement recognizer. The world satisfies the
three property checks used by the statement theorems. Distinct
sources yield distinct made names, but here both searches have the same
source.

## Theorems

The **world property checks** below are `wf-world-property-shapes-p`,
`wf-world-properties-p`, and `wf-world-event-data-p`. The event
interval is `(0, hi]` for the library and `(lo, hi]` for a book.

| Theorem | What it says and what it assumes |
| --- | --- |
| `well-formed-library-statements` | With the world property checks, the statements returned by `bx-library-lines` form a proper list whose lines satisfy the statement recognizer, including its name rules. |
| `well-formed-book-statements` | With the world property checks, the statements returned by `bx-book-lines` form a proper list whose lines satisfy the statement recognizer, including its name rules. |
| `well-formed-library-statement-with-names` | With the world property checks, every individual statement returned by `bx-library-lines` satisfies the statement recognizer, including its name rules. |
| `well-formed-book-statement-with-names` | With the world property checks, every individual statement returned by `bx-book-lines` satisfies the statement recognizer, including its name rules. |
| `well-formed-library-program` | With the world property checks, a property-list world with symbol attachment targets, well-shaped successful translations and ground functions with stored bodies, every program line returned by `bx-library-lines` has the shape of its format. |
| `well-formed-book-program` | With the world property checks, a property-list world with symbol attachment targets and well-shaped successful translations, every program line returned by `bx-book-lines` has the shape of its format. |
| `well-formed-fresh-constraint-name` | For any inputs, `bx-fresh-name` returns `NIL` or a non-keyword symbol in the source function's package that `bx-in-use-p` finds unused in the supplied world. |
| `constraint-statement-or-missing-name-note` | For any inputs, `bx-constrain-stmt` returns one item for the constraint. If a formula has name `NIL`, the item is a note with the functions followed by all non-`NIL` formula names. Otherwise the item is a `constrain` statement. |
| `constraint-missing-name-note-names-introductions` | If any formula has name `NIL`, a name occurs in the note data exactly when it is among the functions or is a non-`NIL` formula name. This uses no world hypothesis. |
| `well-formed-library-notes-include-item` | If a note item occurs among the selected events' items, `bx-library-lines` returns it as a note line with its key and data intact. This uses no world hypothesis. |
| `well-formed-book-notes-include-item` | If a note item occurs among the selected events' items, `bx-book-lines` returns it as a note line with its key and data intact. This uses no world hypothesis. |
| `well-formed-equal-made-names-have-same-source` | Two successful `bx-formula-name` searches from valid sources can return the same symbol only if their source functions, kinds and positions agree. The worlds and the retry numbers may differ. |

The program list recognizer also requires the returned sequence to be
a proper list. The statement theorems accept any translation table.
Only statement items can cause an event's items to be held for later
output, and program-only events supply no statement items.

A valid source, tested by `wf-constraint-name-source-p`, has a symbol
for its function and one of three kinds. The name of a definition or
choice uses its function and position zero. The name of an unnamed
constraint formula uses the constraint owner and a positive formula
position. `wf-constraint-name-word` gives the spelling for each kind
and position. The name search passes over imports from other packages.
The name theorem concerns pairs of searches and allows multiple
searches for one source, as in the nested example.

## Hypotheses and tests

The script saves ACL2's initial world before loading the exporter and
tests the world predicates on that snapshot. It runs the shell's body
translator for the initial export and uses the actual ground function
list read from `spec/ground.txt`. It also tests the hypotheses after
including `std/lists/append`, `misc/defattach-example`,
`std/system/defchoose-queries`, `std/stobjs/1d-arr`,
`misc/hidden-defpkg-checks/top`, `misc/defpun`, and
`std/strings/pretty`, all named in `export/books.txt`.

| Predicate | Condition on the inputs | Tests in `well-formed.sh` |
| --- | --- | --- |
| `wf-world-property-shapes-p` | Stored bodies, theorems and choice axioms are pseudo-terms. Constraint properties and justification records have their ACL2 shapes, and the known package alist has the ACL2 record shape. Unbound properties are allowed. | `INITIAL-PROPERTY-SHAPES` and `SAMPLE-PROPERTY-SHAPES` |
| `wf-world-properties-p` | Stored terms meet the additional variable, lambda, and quoted-data conditions. Formals are distinct legal variables. Initial functions with raw code only need legal formals when they have a stored body, since the core can omit those without one. Package names are nonempty and a package axiom's quoted imports are a symbol list. Sibling function names have the function-name shape. An `mbe` visited when extracting an executable body has a second argument. | `INITIAL-PROPERTY-DETAILS` and `SAMPLE-PROPERTY-DETAILS` |
| `wf-world-event-data-p` | In the export interval, relevant event names have the required shapes and the properties read for the emitted lines are available. This includes a stored body for an emitted logic definition or program stobj definition, a stored formula for a theorem or axiom, a constraint owner with a formula list or the unknown-constraints marker, and the second free-variable list in a strengthened choice axiom when its comparison is recognized. A package event needs the known package alist. | `INITIAL-EVENT-DATA` and `SAMPLE-EVENT-DATA` |
| `plist-worldp` | The world is a proper list of property triples with symbol keys. This supplies the shape of attachment sources. | `INITIAL-TRIPLES` and `SAMPLE-TRIPLES` |
| `wf-world-attachment-targets-p` | Each target in an alist of allowed attachments is a symbol. An attachment property can instead be a symbolic reference or mark attachments as disallowed. | `INITIAL-ATTACHMENT-TARGETS` and `SAMPLE-ATTACHMENT-TARGETS` |
| `wf-translations-p` | Every nonempty successful translation is a term with an executable argument in each `mbe` the executable-body walk visits. Translation failures have no term-shape condition. | `INITIAL-TRANSLATIONS` and `SAMPLE-TRANSLATIONS` |
| `wf-ground-functions-p` | The supplied ground functions are a list of function names with stored bodies. | `INITIAL-GROUND-FUNCTIONS` and `SAMPLE-GROUND-FUNCTIONS` |

ACL2's `pseudo-good-worldp` entails the property shapes in the first
row, by `well-formed-property-shapes-of-pseudo-good-world`. The
entry-point theorems use that projection so that they need only the
checks on stored properties they read.

The script also applies the recognizers to the actual library and book
outputs and admits every proof certificate with skipped proofs, trust
tags and added axioms forbidden. Run from the root of the repository.

```sh
sh export/proofs/well-formed.sh
```

Four tests exercise constraint name search and output.

- `CONSTRAINT-IMPORTED-NAME` exports an encapsulate in a package that
  imports `:|F constraint 1|`. The corollary is named
  `WF-EXAMPLE::|F constraint 1 1|`, the statements are `package`,
  `constrain`, and `define` in that order, and the sole note identifies
  the generated name. The constraint introduces `F` before the
  definition of `G`, which calls it.
- `CONSTRAINT-NAMES-EXHAUSTED` adds an encapsulate to a copy of the
  startup world as event and property records. The constraint has an
  unnamed formula, a named formula and a theorem occupying each of the
  unnamed formula's 1,001 candidate names. `bx-book-lines` returns
  no statements. Its missing-name note lists `WF-EXHAUSTED`,
  `WF-EXHAUSTED-COMPANION` and `WF-EXHAUSTED-LAW`. Its other note
  identifies the formula that no event states.
- `CONSTRAINT-SHARED-IMPORT` uses two packages that import the same
  `ACL2::|F constraint 1|`. Their corollaries are named
  `WF-IMPORT-A::|F constraint 1 1|` and `WF-IMPORT-B::|F constraint 1 1|`.
  The only notes identify those two made names.
- `CONSTRAINT-SHARED-OWNER-EXAMPLE` runs the nested encapsulate above.
  It checks the world property hypotheses, the two distinct statements
  with a shared made name, and the `:NAME-IN-USE` note.

On 2026-11-21, ACL2 8.7 certified all six books and the script printed
`all well-formedness checks passed`.

## Scope of recognition

The recognizers check the word, exact number and shape of fields, and
proper lists. They check symbols for names, nonempty strings for
package names, symbol lists for imports, the two forms of ruler-extenders,
and nonnegative integers for arities in a `constrain` signature. They
check distinct legal formals in definitions and lambdas, and each
`choose` variable list, including the nonempty bound list and the length
of the optional second free list. An `attach` line has two symbols.

A term is a legal variable, a two-element quote of a datum, a call of
a function symbol with term arguments, or a lambda application with
the same number of actuals as formals. A lambda body is itself a term
with every free variable among the lambda's formals. Quoted data may
contain any of the seven kinds of data in the language.

The checker still determines whether symbols exist in the declared
packages, whether imports satisfy the package admission rules, and
whether names are fresh and permitted in the input. This includes the
rule against a book defining a Common Lisp function name. It also
determines which functions are in use with which ordinary arities,
whether definition bodies use only their formals, whether the three
lists of choice variables have the required disjointness, and whether
choice bodies refer only to their allowed variables. The checker is
responsible for the proofs needed to admit statements. Dependencies
between an attachment and the functions it names are a runner concern.

The theorems concern the lines that are returned, including any lines
returned when the library's ordering walk uses up its fuel. Completeness,
order, faithfulness to the ACL2 events, and guard verification are
separate properties. Notes and prover's aids are separate return
values. Printing, reading and the bytes written to files are outside
this data-level property.
