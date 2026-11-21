# Exporter guards

The core runs in ACL2 logic mode. The guard proofs certify the calls made
by the three entry functions. ACL2's `verify-guards` events identify
each result by the function whose guard is proved.

| Guard verification event | Statement |
| --- | --- |
| `verify-guards bx-translation-requests` | With integer event limits and a property-list world whose event tuples and definition forms have the required shape, the translation-request walk only makes calls within their guards. |
| `verify-guards bx-library-lines` | With an integer event limit, a symbol list of ground functions, well-shaped translations, and an export world with the required formals, the library exporter only makes calls within their guards. |
| `verify-guards bx-book-lines` | With integer event limits, directory strings, a symbol list of ground functions, well-shaped translations, and an export world with the required formals, prover-aid declarations, and book records, the book exporter only makes calls within their guards. |

On these inputs ACL2 can run the core as compiled Common Lisp and obtain
the values of its logical definitions.

`export/book.sh` includes the guard book and enables guard checking.
The shell uses `ec-call` at the boundary to the core, so ACL2 checks
the declared guard at entry and uses compiled code for the calls
within the core.

## Entry inputs

ACL2's predicate `pseudo-termp` recognizes the form of a translated
term. The forms are symbol variables, quoted constants, function
applications, and lambda applications.

- Event limits are integers. The request walk uses an ACL2 property-list
  world, recognized by `plist-worldp`, with the event records recognized
  by `bx-event-world-p`. The latter checks the fields read by the
  exporter, including the shapes of the names and compact definition
  forms.
- Both line exporters use `bx-export-world-p`. This includes the
  event-record checks and checks the stored properties used for terms,
  formals, constraints, event numbers, justifications, and attachments.
  It requires the current known-package table and the formals
  that the event readers look up. For an encapsulate with a signature,
  the constraint owner has a list of pseudo-terms or ACL2's mark
  for unknown constraints. For a strengthened choice axiom, the second
  list of free arguments has the length needed for substitution.
- The ground functions form a symbol list, and each of them and each
  ACL2 primitive has formals in the world. The translation results
  satisfy `bx-translations-p`. They form an association list with
  accessible status fields and pseudo-terms for successful translations.
- The book exporter takes integer values for the startup and book event
  limits and strings for the system book directory and the current
  directory. It also uses `bx-world-aids-p` for the declarations read
  from stored definition forms. The predicate `bx-book-globals-p`
  checks the current included-book and trust-tag records and the
  presence of the redefinition flag.

The world checks use the forms that the core reads and the shapes
required for its calls. They scan the supplied world, including event
records outside the selected range. They allow world properties
unrelated to export to have arbitrary values.

## Running the checks

Run `sh export/proofs/guards.sh` from the repository root. It certifies
the guard books, checks the certificate annotations for skipped proofs,
added axioms and trust tags, and checks the guard verification status
of every function defined in the core and of `bm-line`.

The script evaluates all three declared guards on ACL2's startup
world, then on the worlds obtained by successively including
`misc/hidden-defpkg-checks/top`, `misc/defpun`, `std/alists/alist-equiv`,
`std/stobjs/absstobjs`, and `misc/dft-ex`. It reads the ground
definition names from `spec/ground.txt`, takes the event limits and
directory strings from ACL2, and uses the shell to translate the
requested bodies in the live ACL2 session. The tests evaluate the
guards on the saved world values themselves.

The proofs start from the supplied world and translations. ACL2's
construction of the world, the shell's translation and source reading,
and the bytes written to files are outside the guard theorems. The
other exporter proof books cover the interpretation and structure of
the lines.

## Certification results

On 2026-11-21, `sh export/proofs/guards.sh` under ACL2 8.7 printed
`all guard checks passed` in 183 wall-clock seconds. All three entry
guards held on all six worlds. ACL2 reported verified guards for the
140 core functions and the 49 supporting predicates. The certificate
checks found no skipped proofs, added axioms, or trust tags.

Book sizes are from `wc -lc export/proofs/guards*.lisp` on 2026-11-21.
Certification times are the individual times reported by ACL2.

| Book | Lines | Bytes | Seconds |
| --- | ---: | ---: | ---: |
| `guards-events.lisp` | 113 | 3,543 | 0.30 |
| `guards-data.lisp` | 294 | 12,513 | 0.62 |
| `guards-terms.lisp` | 236 | 8,109 | 1.91 |
| `guards-items.lisp` | 920 | 38,105 | 44.40 |
| `guards-report.lisp` | 232 | 8,897 | 19.68 |
| `guards-lines.lisp` | 332 | 13,181 | 46.43 |
| `guards.lisp` | 39 | 1,903 | 0.11 |
| Total | 2,166 | 86,251 | 113.45 |

## Export run

On 2026-11-21, `sh export/run.sh` under ACL2 8.7 exported the library
and all 460 books and confirmed them on readback. With one ACL2 worker,
the script reported 356 seconds for export and readback. The full
command took 510 seconds, including the format checks and size report.
`checks/reader.py` read every file.

On 2026-11-21, `sh export/proofs/round-trip.sh`,
`sh export/proofs/structure.sh`, `sh export/proofs/well-formed.sh`,
and `sh export/proofs/faithful.sh` passed. So did `sh checks/run.sh`,
`sh runner/test.sh`, and `sh checker/test.sh`. The runner compiled the
program text of the library and all 460 books.
