# The exporter

The exporter of `PLAN.md`, step 2, is run by ACL2. For ACL2's built-in library and for each book that `books.txt` lists, it writes, in the formats of `spec/formats.md`, the statements, the program text for a runner, the prover's aids and notes; `readback.lsp` has ACL2 read each file back and confirm every line. One command runs it all, from the root of the repository: `sh export/run.sh`.

It is split into a **core**, a pure function from ACL2's world to the lines written, which is meant to be proved correct in ACL2 (`PLAN.md`, step 4b), and a **shell**, which does what needs the state of an ACL2 session and is not proved. This file is for whoever proves theorems about the core: what each part holds, what goes in and out of the core, and what lies outside it. Paths are given from the root of the repository.

## The files

| File | What it is |
|---|---|
| `export/core.lisp` | The core: an ACL2 book, 130 functions, all in logic mode, with no state. |
| `checks/canon.lisp` | The printer of the formats: an ACL2 book, 12 functions in logic mode, with no state. `(bm-line WORD ARGS)` is the text of a line. It is the one printer of the repository: the scripts of `checks/` and of the runner's tests load it through `checks/canon.lsp`, which adds two functions that write lines to a file. |
| `export/export.lsp` | The shell, in program mode: it takes the world from the session, does the translations the core asks for, reads the books' sources for their local events, prints each line with `bm-line` and writes the files. |
| `export/certify.sh` | Has ACL2 certify the two books into `build/export/acl2/` when they change. |
| `export/book.sh` | Exports one book, or the library, in one run of ACL2: it includes the book, records the range of events it added, includes the two certified books, loads the shell, calls it, and loads and runs the read-back check. |
| `export/run.sh` | Runs `book.sh` on the library and on every book of `books.txt`, two at a time, then `checks/reader.py` on every file, and writes `build/export/summary.txt`. |
| `export/readback.lsp` | The read-back check: a reader of the formats and a comparison of each line with the world, written apart from the exporter. It holds the one function in raw Lisp (to intern a symbol of a hidden package). |
| `export/measure.py` | The counts and sizes of the summary. |
| `export/books.txt`, `export/choice.lisp` | The books exported, and a book of two cases of the exporter's own. |

## The core

Every function of `core.lisp` is in logic mode. ACL2 admits each with at most a declared measure: no hint, no lemma, and no book of lemmas but `system/remove-guard-holders-weak` of ACL2's distribution, which puts one function of ACL2 in logic mode (below). The guards are not verified (`set-verify-guards-eagerness 0`). The shell runs the core with guard checking off, as for a program.

Four functions recur in a way whose end is not plain from their arguments, and count their steps with an argument `fuel`, with a bound that is never reached:

| Function | What `fuel` counts, and its bound |
|---|---|
| `bx-fresh-name` | The numbers tried for a made name; 1,000. |
| `bx-bound-many` | The bound variables read from an axiom of choice; the number of the lambda's formals. |
| `bx-local-order` | The rounds of ordering the functions of a `defstobj`; their number. |
| `bx-walk` | The steps of the walk that orders the library's definitions; `bx-steps`, three for each statement and one for each function it calls. |

`bx-mv-nths` has the declared measure `(nfix (- k i))`. Two definitions of the printer, `bm-obj` and `bm-tail`, have declared measures `(* 2 (acl2-count x))` and `(+ 1 (* 2 (acl2-count x)))`.

### The entries

The world `wrld` is ACL2's world, a list of triples `(SYMBOL PROPERTY . VALUE)`, newest first. Events are numbered; a range of events is given by `lo` and `hi`, the events numbered above `lo` and at most `hi`. A line is a list `(WORD ARGS)`: `WORD` a string, `ARGS` the list of data after it, whose text is `(bm-line WORD ARGS)`.

| Function | Takes | Returns |
|---|---|---|
| `bx-translation-requests` | `lo hi wrld` | The bodies the shell must translate: a pair `(FN . BODY)` for each function in program mode in the range whose body the world does not store (the functions ACL2 starts with), `BODY` as the defining event wrote it. |
| `bx-library-lines` | `ground-fns hi translations wrld` | `(mv statements program notes)`, the lines of `library.statements`, `library.program` and `library.notes`. `ground-fns` are the functions that `spec/ground.txt` defines; `hi` is the last event of the world ACL2 starts with; `translations` pairs each requested function with `(:ok . TERM)` or `(:error . MESSAGE)`. |
| `bx-book-lines` | `ground-fns boot-hi lo hi translations books-dir cbd wrld` | `(mv statements program notes aids)` for a book whose inclusion added the events above `lo` and at most `hi` to the world ACL2 starts with, whose last event is `boot-hi`. `books-dir` is the directory of ACL2's books and `cbd` the directory in which ACL2 runs, by which books are named in the notes. `aids` are the aids that the events give; the shell puts the local events before them and adds a note for each book whose source it could not read. |

The shell also calls `bx-events`, `bx-book-files`, `bx-book-name`, `bx-note`, `bx-select` and `bx-note-lines`.

### The sections of `core.lisp`

0. Event tuples and guard holders: the parts of ACL2's record of an event, read as ACL2's own accessors read them, and the removal of guard holders.
1. Small tools: kinds of name, made names for formulas, what a statement introduces and uses.
2. The events of a range, each paired with the innermost `encapsulate` with a signature that contains it.
3. Terms: beta reduction, and the executable half of an `mbe`.
4. Functions introduced by choice: the axiom of `spec/logic.md`, and reading its parts from the axiom ACL2 stores.
5. The items of one event: statements, program text and notes, by the kind of event.
6. Selecting items.
7. The library: its order.
8. A check of the order: every function a line calls is in use, every name it introduces is new, every symbol's package is declared.
9. The ground theory, as the check starts from it.
10. Attachments.
11. Notes, counts, and the library's lines.
12. The prover's aids of the events.
13. A book's lines.

## ACL2's functions in program mode

The core calls no function of ACL2 that is in program mode in ACL2 8.7, the version that `checks/version.lsp` names. For each that the exporter needs:

| ACL2's function | What the core does |
|---|---|
| `access-event-tuple-number`, `-depth`, `-type`, `-namex`, `-form`, `-symbol-class`, `-skipped-proofs-p` | Definitions of its own, `bx-ev-number` and the rest, which read the event tuple as ACL2's do (section 0). |
| `signature-fns` | A definition of its own, `bx-signature-fns`. |
| `lookup-world-index` | A definition of its own, `bx-world-at`, which walks the world to the landmark of an event. |
| `remove-guard-holders` | `remove-guard-holders-weak`, which the book `system/remove-guard-holders-weak` of ACL2's distribution puts in logic mode, called as ACL2 calls it, with `t` for the value of `remove-guard-holders-lamp`, whose attachment always gives `t`. ACL2's function then also simplifies quoted lambda objects that it finds dirty; the core does not. On the library and the 460 books of `books.txt` the output is the same either way (the comparison of step 4b). |
| `translate-cmp`, with `default-state-vars` and `fms-to-string` | Called by the shell, for the bodies the core requests; the core takes the results as `translations`. |
| `read-object`, `open-input-channel`, `set-current-package`, `current-package`, `system-books-dir`, `cbd` | Called by the shell only, to read the local events of the books and to name the books. |

The functions of ACL2 that the core calls are in logic mode: among them `getprop` (through `getpropc`), `global-val`, `formals`, `constraint-info`, `unknown-constraints-p`, `flatten-ands-in-lit`, `subcor-var`, `all-fnnames1`, `merge-sort-lexorder`, `explode-nonnegative-integer`, `intern-in-package-of-symbol`, and `hons-acons`, `hons-get` and `fast-alist-free`, whose logical meaning is that of ordinary association lists.

## What the shell does

`export.lsp` holds 13 functions in program mode. For the library, `bx-export-library` takes the world from the session, asks the core for the bodies to translate, translates each with `translate-cmp`, calls `bx-library-lines`, and writes the three files. For a book, `bx-export-book` does the same, and before it reads the source of each book in the range with ACL2's reader, in the package the book's first form names, and collects its local events (at the top level and inside `encapsulate`, `progn` and `defsection`). Each line is printed with `bm-line` and written with a newline. `book.sh` sets guard checking off before the export and on again before the read-back check.

## What lies outside the proofs

- That ACL2's world means what the core takes it to mean: that a property such as `unnormalized-body` or `constraint-lst-etc` is what ACL2's documentation and source say it is.
- What the shell computes: the translations of the bodies of the functions in program mode that ACL2 starts with, and the local events read from the books' sources.
- The bytes that reach the disk, which ACL2's `princ$` writes.
- The one function in raw Lisp of the read-back check, and the shell scripts and the Python of `run.sh`, `book.sh`, `certify.sh` and `measure.py`.

## What will make the proofs hard

- **The round trip.** `checker/read.lisp` does not give back an ACL2 symbol as it is: it holds the symbol whose text is `P::N` as the symbol of the package `BOYMOO` whose name is that text, and `COMMON-LISP::NIL` and `COMMON-LISP::T` as `NIL` and `T`; and it reads a line against the packages declared before it, refusing a symbol whose package is not declared or that its package imports. So the theorem relates the printer's text of a datum to the reader's form of that datum, given packages that declare every symbol in it, rather than to the datum itself. The reader also works on the characters of a whole line, with a stack of its own, where the printer builds the text in reverse.
- **What the world is.** Faithfulness can only be stated against ACL2's properties as the core reads them: `getprop` on the world, a list of triples, and the event tuples, whose shape (section 0) is ACL2's convention and no theorem of ACL2's. Completeness needs the same: the names an event introduces are its `namex`.
- **The bounds.** Each function that counts its steps with `fuel` gives a result that ignores the bound only if the bound is large enough: that has to be proved for each, from what the steps do (for the walk of the library, that each statement is pushed once).
- **The guards.** The core takes the world and data read from it; verifying its guards needs that these have the shapes ACL2 gives them (true lists, symbols, terms), which ACL2 keeps as invariants of its world and does not state.
- **The names of constraint formulas.** A formula of a constraint is named by matching it with the formulas of the encapsulate's events, after `flatten-ands-in-lit` and `remove-guard-holders-weak`; faithfulness for a `constrain` statement therefore says that the formulas cover ACL2's constraint, conjunct by conjunct, not that they are equal to it.
