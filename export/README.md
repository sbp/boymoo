# The exporter

The exporter of `PLAN.md`, step 2, is run by ACL2. For ACL2's built-in library and for each book that `books.txt` lists, it writes, in the formats of `spec/formats.md`, the statements, the program text for a runner, the prover's aids and notes; `readback.lsp` has ACL2 read each file back and confirm every line. One command runs it all, from the root of the repository: `sh export/run.sh`.

It is split into a **core**, a pure function from ACL2's world to the lines written, about which theorems are proved in ACL2 (`export/proofs/`; `PLAN.md`, step 4b, lists them), and a **shell**, which does what needs the state of an ACL2 session and is not proved. This file is for whoever reads or extends those proofs: what each part holds, what goes in and out of the core, and what lies outside it. One command runs every proof, from the root of the repository: `sh export/prove.sh`. Paths are given from the root of the repository.

## The files

| File | What it is |
|---|---|
| `export/core.lisp` | The core: an ACL2 book, 189 functions, all in logic mode and each with a declared guard, with no state. |
| `checks/canon.lisp` | The printer of the formats: an ACL2 book, 12 functions in logic mode, with no state. `(bm-line WORD ARGS)` is the text of a line. It is the one printer of the repository: the scripts of `checks/` and of the runner's tests load it through `checks/canon.lsp`, which adds two functions that write lines to a file. |
| `export/export.lsp` | The shell, in program mode: it takes the world from the session, does the translations the core asks for, reads the books' sources for their local events, prints each line with `bm-line` and writes the files. It calls the core through `ec-call`. |
| `export/certify.sh` | Has ACL2 certify the two books into `build/export/acl2/` when they change; with `--guards`, also the seven books of `export/proofs/guards*.lisp` that verify the guards of the core, and with `--fresh-guards`, those seven again from the start. |
| `export/proofs/` | The proofs about the core and the printer, in five sets, `round-trip`, `guards`, `structure`, `well-formed` and `faithful`: for each, its ACL2 books, its tests, a script `NAME.sh` that certifies the books and runs the tests, and a report `NAME.md` that gives every theorem, its hypotheses and their tests. |
| `export/prove.sh` | Runs `certify.sh` and the five scripts of `export/proofs/`, and ends with `all proofs passed` or `some proofs failed`. |
| `export/book.sh` | Exports one book, or the library, in one run of ACL2: it has `certify.sh --guards` certify the books of the exporter, writes `build/export/ground-fns.lsp`, the functions that `spec/ground.txt` defines, when it is missing or older than that file, includes the book, records the range of events it added, includes the printer and the book `guards`, which includes the core with its guards verified, loads the shell, sets guard checking on, calls the shell, and loads and runs the read-back check. |
| `export/run.sh` | Runs `book.sh` on the library and on every book of `books.txt`, two at a time, then `checks/reader.py` on every file, and writes `build/export/summary.txt`. |
| `export/readback.lsp` | The read-back check: a reader of the formats and a comparison of each line with the world, written apart from the exporter. It holds the one function in raw Lisp (to intern a symbol of a hidden package). |
| `export/measure.py` | The counts and sizes of the summary. |
| `export/books.txt`, `export/choice.lisp` | The books exported, and a book of two cases of the exporter's own. |

## The core

Every function of `core.lisp` is in logic mode, with a declared guard. ACL2 admits each with at most a declared measure: no hint, no lemma, and no book of lemmas but `system/remove-guard-holders-weak` of ACL2's distribution, which puts one function of ACL2 in logic mode (below). 49 of the functions are predicates for the guards, which say what shape the world, its records of events, the translations and the data passed from one function to another must have. The book declares the guards and does not verify them (`set-verify-guards-eagerness 0`); the books of `export/proofs/guards*.lisp`, which include it, verify the guard of every function, and the shell runs the core with guard checking on (below).

Four functions recur in a way whose end is not plain from their arguments, and count their steps with an argument `fuel`, with a bound that is never reached:

| Function | What `fuel` counts, and its bound |
|---|---|
| `bx-fresh-name` | The numbers tried for a made name; 1,000. A name in use, a keyword, or a symbol of a package other than the function's (one the package imports) is passed over, so that no two formulas get one made name; if every name tried is passed over, the result is `NIL`, and the constraint that needed it gets a note in place of its statement, naming its functions and the names of its other formulas. |
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
| `bx-book-lines` | `ground-fns boot-hi lo hi translations books-dir cbd wrld` | `(mv statements program notes aids)` for a book whose inclusion added the events above `lo` and at most `hi` to the world ACL2 starts with, whose last event is `boot-hi`. `books-dir` is the directory of ACL2's books and `cbd` the directory in which ACL2 runs, by which books are named in the notes. `aids` are the aids that the events give; the shell puts the local events before them and adds a note for each book whose source it could not read. The statements of the library are computed again, and checked before the book's; if a line of them cannot be admitted in order, the book's notes say so. |

The shell also calls `bx-events`, `bx-book-files`, `bx-book-name`, `bx-note`, `bx-select` and `bx-note-lines`.

The guard of each entry is a condition on the world and on what the shell hands the core. That of `bx-translation-requests` is that `lo` and `hi` are integers and that the world is a list of property triples whose records of events have the shapes the core reads (`bx-event-world-p`). That of `bx-library-lines` is that `hi` is an integer, `ground-fns` a list of symbols, each with stored formals, as each of ACL2's primitives has, `translations` a list of pairs whose successful translations are terms (`bx-translations-p`), and that the world meets `bx-export-world-p`: the records of events as above, every stored value of each property the core reads of the type it is read as, the table of known packages of ACL2's shape, and stored formals and constraints for the functions that events introduce. That of `bx-book-lines` adds integers for `boot-hi` and `lo`, strings for `books-dir` and `cbd`, declarations of the shape from which the aids are read (`bx-world-aids-p`), and ACL2's records of trust tags, included books and redefinition (`bx-book-globals-p`). `PLAN.md`, step 4b, property 2, says what each holds, and `export/proofs/guards.md` gives the tests.

### The sections of `core.lisp`

0. Event tuples and guard holders: the parts of ACL2's record of an event, read as ACL2's own accessors read them, and the removal of guard holders.
1. Small tools: kinds of name, made names for formulas, what a statement introduces and uses.
2. The events of a range, each paired with the innermost `encapsulate` with a signature that contains it.
3. Terms: beta reduction, and the executable half of an `mbe`.
4. Functions introduced by choice: the axiom of `spec/logic.md`, and reading its parts from the axiom ACL2 stores.
5. The items of one event: statements, program text and notes, by the kind of event. The items of an event inside an encapsulate with a signature that call a function of its constraint, or a function of items so placed, stand right after the constraint.
6. Selecting items.
7. The library: what the ground theory holds, which it leaves out (the definitions of the ground theory's functions, ACL2's 84 axioms, its packages, `T` and `NIL`; an axiom of the world not among the 84 has its own statement), and its order.
8. A check of the order: every function a line calls is in use, every name it introduces is new, every symbol exists (its package is declared, and imports no symbol of its name; `spec/language.md`, section 2).
9. The ground theory, as the check starts from it: its functions, its names, among them ACL2's 84 axioms (`*bx-ground-axioms*`), and its packages with their imports.
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

`export.lsp` holds 13 functions in program mode. For the library, `bx-export-library` takes the world from the session, asks the core for the bodies to translate, translates each with `translate-cmp`, calls `bx-library-lines`, and writes the three files. For a book, `bx-export-book` does the same, and before it reads the source of each book in the range with ACL2's reader, in the package the book's first form names, and collects its local events (at the top level and inside `encapsulate`, `progn` and `defsection`). Each line is printed with `bm-line` and written with a newline. `book.sh` sets guard checking on before the export, and the shell calls each function of the core through `ec-call`, so that ACL2 checks the function's guard on the arguments given and then runs the core's compiled code. A guard that does not hold ends the export with an error, before any file of it is written.

## What lies outside the proofs

- That ACL2's world means what the core takes it to mean: that a property such as `unnormalized-body` or `constraint-lst-etc` is what ACL2's documentation and source say it is.
- What the shell computes: the translations of the bodies of the functions in program mode that ACL2 starts with, and the local events read from the books' sources.
- The bytes that reach the disk, which ACL2's `princ$` writes.
- The one function in raw Lisp of the read-back check, and the shell scripts and the Python of `run.sh`, `book.sh`, `certify.sh` and `measure.py`.
- The prover's aids, of which no theorem speaks.
- Whether the worlds that ACL2 makes meet the guards of the core's entries. `export/proofs/guards.sh` tests them on six worlds, and ACL2 checks them on each world exported, but no theorem says so.
- Two cases in which the lines differ from what ACL2 holds, each reported by a note: a group of mutually recursive functions that declare different ruler-extenders, for which the `define` statement gives the first function's (`PLAN.md`, "Undecided"); and two nested encapsulates with signatures whose constraint ACL2 records once, under the outer function, for which the core writes that constraint twice, as a `constrain` statement at each, both with the same made name for the same conjunct, so that a checker refuses the second (`export/proofs/structure.md`).

## What the proofs rest on

- **The round trip.** `checker/read.lisp` does not give back an ACL2 symbol as it is: it holds the symbol whose text is `P::N` as the symbol of the package `BOYMOO` whose name is that text, and `COMMON-LISP::NIL` and `COMMON-LISP::T` as `NIL` and `T`; and it reads a line against the packages declared before it, refusing a symbol whose package is not declared or that its package imports. So the theorem relates the printer's text of a datum to the reader's form of that datum, given packages that declare every symbol in it, rather than to the datum itself; that form determines the datum (`rt-datum-form-injective`).
- **What the world is.** Faithfulness is stated against ACL2's properties as the core reads them: `getprop` on the world, a list of triples, and the event tuples, whose shape (section 0) is ACL2's convention and no theorem of ACL2's. Completeness rests on the same: the names an event introduces are its `namex`. The theorems take the shapes they need as hypotheses, which their scripts test on ACL2's worlds.
- **The bounds.** The bound of the walk of the library is proved to be large enough (`structure-walk-library-fuel-suffices`). The theorems have no hypothesis about the other three bounds: what those functions give is compared with the world, or checked for order, or, for `bx-fresh-name`, gives a note when the bound is reached.
- **The guards.** The core takes the world and data read from it; verifying its guards needs that these have the shapes ACL2 gives them (true lists, symbols, terms), which ACL2 keeps as invariants of its world and does not state. The guards of the entries state them, with the predicates named above, and ACL2 proves that every call the core makes from there meets the guard of the function called; whether a world meets the guards of the entries is tested, not proved.
- **A choice of no formals.** For a function with no formals introduced with `:strengthen t`, ACL2 stores the longer axiom of `spec/logic.md`, section 6, and the core writes the statement with `FREE2` `NIL`, whose axiom is the basic one (`bx-choose-items`). Faithfulness for a `choose` statement says that the stored axiom is, up to beta reduction, either the statement's axiom or, for such a function, the longer axiom built with the second call the same as the first, which adds only that the call equals itself.
- **What is held back.** The items of an event inside an encapsulate that call a function of its constraint stand after the constraint (`bx-items`), so the order of a book's statements is that of ACL2's events except for these. Where the formulas of a constraint call a function introduced by an item held back after it, the check of section 8 writes a note, and the theorem of order allows for it.
- **The names of constraint formulas.** A formula of a constraint is named by matching it with the formulas of the encapsulate's events, after `flatten-ands-in-lit` and `remove-guard-holders-weak`; faithfulness for a `constrain` statement says that the formulas cover ACL2's constraint, conjunct by conjunct, not that they are equal to it.
