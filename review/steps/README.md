# The book of steps

Run from the repository root with ACL2 8.7, Python 3.8 or later and Node on the
`PATH`.

```sh
sh review/steps/run.sh
```

The command checks `spec/example` and every case in `checker/cases` and
`checker-js/cases` whose recorded verdict is `accepted` or `provisional`
and that has a step in `proofs.txt` or `library-proofs.txt`. It compares
both checkers' verdicts with the recorded verdict. After the cases it
checks the checker's own source using `build/checker/checker.statements`
and `build/self/checker.proofs`, with empty library inputs. It runs
`sh review/self/run.sh` if either source input is missing or empty,
with output in `build/steps/self-build.log`.
The source build also uses the tools for the exporter and reference runner
listed in `DETAILS.md`. Both checkers must give `accepted` for the source.

The script writes a book for each input under `build/steps/`, with the
source book at `build/steps/self/book.lisp`. It reports each proof by entry
name, input and line range, then gives separate totals for the cases and
the source as well as an overall total.
The exit status is zero when every replayable proof certifies and every
exclusion is accounted for. An unexpected ACL2 failure gives a nonzero
exit status.

The same command takes a library, statements, proofs and an optional
fourth file for the library's proofs. An omitted fourth file means empty
library proofs. It puts the book, its package commands, the certificate
and the ACL2 log under `build/steps/input/`. An empty file is a valid library.

```sh
sh review/steps/run.sh build/steps/empty spec/example/statements.txt spec/example/proofs.txt
```

The command creates `build/steps/empty` itself. It uses one ACL2 process at
a time. Certification checks both the package commands and the certificate
annotations. The certificate must have empty annotations for skipped
proofs and trust tags. The only `defaxiom` events come from explicit input
`axiom` statements.

## From the checker to the book

`trace.lsp` calls `BOYMOO::CHECK-FOUR` in ACL2 and replays successful
inputs through `BOYMOO::PREPARE-STATEMENT`, `BOYMOO::ADMIT` and
`BOYMOO::PROOF-LINE`. It reads the library with its proofs first, then
uses the resulting world to read the statements with their proofs. A
library statement with obligations is given at its `skip` or when the
library's proofs have ended. After a step, `PROOF-LINE` holds the
computed clause at the head of its history.
The trace records that clause beside the step's input line. A cons in the
trace has two references to earlier objects, so repeated subterms keep
their sharing across lines.

`book.py` renders the clauses as ACL2 formulas. The empty clause becomes
`nil`, a unit clause becomes its literal, and other clauses become
disjunctions. Each step gets its own `defthm` with `:rule-classes nil`.
A name such as `BOYMOO-STEP-12` identifies line 12 of the book's proofs.
`BOYMOO-STEP-LIBRARY-12` identifies line 12 of the library's proofs.
The prefix is chosen to avoid input names. A repeated subterm in a large
literal can be bound once with `let*`, as in the proof budget case. Each
binding denotes the subterm in its original scope.

The trace preserves the reader's qualified names. The correspondence
between these names and ACL2 data is proved by the books
`export/proofs/round-trip*.lisp`. The renderer escapes native names and
strings for ACL2's reader. A `make-event` can insert a character by its
code or intern a symbol relative to a hidden package's witness.

| Input | ACL2 event |
| --- | --- |
| `package` | A `defpkg` in the certification commands, with the declared imports. ACL2 reads packages before the book, so a package that opens after a hidden declaration is open throughout certification. |
| `hidden-package` | An auxiliary book supplies a package witness. A second book includes the first locally and exports the witness, so ACL2 can intern in the package during certification while keeping it hidden. |
| `define` | `defun` or `mutual-recursion`, with the stored body and ruler-extenders. Both halves of an `mbe` appear in the translated `return-last` form. For a `measure` entry the definitions use its measures with `o<`, and cite the last steps of the termination proofs. When every obligation is available the hint uses ACL2's minimal theory. A constant true test around a measured body supplies the single result signature when ACL2's translator requires a base branch. |
| `constrain` | An `encapsulate` with one signature per function. Each local definition calls its witness on the signature's arguments. A multiple-value witness returns its results as a list using `mv-list`. Each exported theorem opens the local definitions and uses the corresponding witness proof. A constraint with no formulas can use constant witnesses. |
| `choose` | A statement or proof entry becomes `defchoose` with the given bound and free variables, body and strengthening flag. A fact citation for strengthened choice instantiates ACL2's generated second set of variables with the names in the input. |
| `theorem` and `lemma` | A named `defthm` uses the last step at `qed`. A `define` entry in the proofs is admitted at the point where the checker admits it. |
| `axiom` | A `defaxiom` for the exact input formula. Proofs that cite it use the supplied assumption. |
| `reserve` and repeated lines | These contribute no new ACL2 events. |

Termination proofs can mention the functions whose admission they justify.
In that case ACL2 first proves the steps about fresh, unconstrained
functions of the same arities. The definition cites those results by
functional instantiation. After the definition, the book proves the
original step conclusions with the real function names.

For library events already in ACL2's world, the book checks the definition
or theorem against the stored one. For existing constrained functions it
checks the arities and uses stored theorems or proves the constraint
formulas with hints from their origins. For a given constraint without a
matching native event, the book tries constant `nil` witnesses. ACL2 must
admit additional library events and events with a `skip` entry by ordinary
proof. If one is unavailable, the replay reports it and certifies steps
whose premises and functions are available. The refused event and ACL2
log are saved beside the book.

## Step hints

| Rule | Hint |
| --- | --- |
| `fact` | Use the named axiom, theorem, definition, package fact or choice formula. For a string-named fact of the ground theory, including the built-in clauses about `acl2-count`, ACL2 proves the supplied clause directly. |
| `instantiate` | Use `:instance` of the premise theorem with the simultaneous substitution. ACL2 can ignore bindings for variables absent from the premise. |
| `subsume` | Use the premise in ACL2's minimal theory. The clause follows by propositional reasoning. |
| `cut` | Use both premise theorems so ACL2 has the complementary literals and their respective remaining disjuncts. |
| `substitute` | Use both premise theorems and split on the equality at the head of the first. In the minimal theory ACL2 uses equality of arguments to justify the literal at the position selected by the checker. |
| `beta` | ACL2 simplifies the lambda application and the substituted body with induction disabled. |
| `compute` | ACL2 evaluates the primitive on the constants with induction disabled. The claimed value is the one in the checker trace. |
| `induct` | Derive a native induction scheme from the measure and substitutions, then use the induction conclusion at the original measure. |

For `induct`, the generated recursive function has a separate ordinal
argument `r`. For each substitution `s` it recurs with the substituted
arguments and measure `m/s` under the tests `(o-p (m/s))` and
`(o< (m/s) r)`. ACL2 admits the function using `o<`. The induction proves
that `phi` holds when `r` equals `m`. It uses the first premise at the
substitutions for the ordinal conditions, and the second premise with
the induction hypotheses for `phi`. Instantiating `r` with `m` gives
the exact step formula. With no substitutions the second premise gives
`phi` directly.

## Results

On 2026-11-24, this command with ACL2 8.7 took 65.57 seconds and
exited with status 0. It printed `all replayable proofs passed`.

```sh
SBCL_USER_ARGS="--dynamic-space-size 1500" sh review/steps/run.sh
```

The 106 cases took 46.72 seconds. The source group took 13.01 seconds
with both source inputs present. ACL2 reports 7.92 seconds for certifying
the source book in `build/steps/self/book.log`.

| Input | Proofs certified | Steps certified |
| --- | ---: | ---: |
| Cases with verdict `accepted` | 139 of 142 | 469 of 472 |
| Cases with verdict `provisional` | 85 of 99 | 185 of 219 |
| All cases | 224 of 241 | 654 of 691 |
| Checker source with verdict `accepted` | 322 of 322 | 7,827 of 7,827 |
| All inputs | 546 of 563 | 8,481 of 8,518 |

Of the 24 library proofs and their 42 steps, 22 proofs and 40 steps
certified. The source certificate covers 262 termination obligations and
60 lemmas.
The source book replays the exported bodies and admits the definitions
from those proofs in a fresh ACL2 world with the `BOYMOO` package. Its
certificate has empty annotations for axioms, skipped proofs and trust tags.

| Input | Primary book files | Book bytes | Certificates | Certificate bytes |
| --- | ---: | ---: | ---: | ---: |
| Cases | 106 | 1,285,642 | 105 | 1,328,637 |
| Checker source | 1 | 11,494,031 | 1 | 6,605,784 |

File counts and byte sizes come from this command after the run on
2026-11-24.

```sh
python3 - <<'PY'
from pathlib import Path
root = Path("build/steps")
for group, suites in (("cases", ("spec", "checker", "checker-js")),
                      ("source", ("self",))):
    books = [book for suite in suites for book in (root / suite).rglob("book.lisp")]
    for suffix in (".lisp", ".cert"):
        files = [book.with_suffix(suffix) for book in books
                 if book.with_suffix(suffix).is_file()]
        print(group, suffix, len(files), sum(file.stat().st_size for file in files))
PY
```

### Proofs whose context could not be admitted

Three proofs of inputs with verdict `accepted` each have one unavailable
step.

| Case under `checker-js/cases/` | Lines of `proofs.txt` | Reason |
| --- | --- | --- |
| `library-lisp-function` | 2–3 | The proof cites the equation of the new `COMMON-LISP::C-NEW` supplied by the library. ACL2 admits functions in the Common Lisp package during bootstrap only. |
| `library-proofs-lisp-recursive` | 2–3 | The proof cites the equation of the new `COMMON-LISP::C-LEN` supplied by the library. Its two termination proofs certify independently. ACL2 refuses to introduce the function in the Common Lisp package. |
| `package-code-order` | 2–3 | The step computes the imports of the package named `"P\E9"`. ACL2 on the tested Lisp treats code 233 as lower case and refuses the package declaration. ACL2 Core tests only ASCII lower case. See `EDGE-CASES.md`, entry 7.2. |

Four provisional proofs depend on equations of given identity functions.
ACL2 fails to admit the constraints because the constant `nil` witnesses
leave the goal `(equal nil x)` for arbitrary `x`.

| Case under `checker/cases/` | Input and proof lines | Given constraint |
| --- | --- | --- |
| `provisional-library-proofs-end-between-statements` | `proofs.txt` 5–6 | `ACL2::LIBRARY-IDENTITY` on line 3 of `library.txt`, given at the end of `library-proofs.txt`. |
| `provisional-library-proofs-interleaved` | `library-proofs.txt` 6–7 and 9–10, and `proofs.txt` 2–3 | `LIBRARY-EXAMPLE::IDENTITY` on line 3 of `library.txt`, given by `skip` on line 4 of `library-proofs.txt`. |

The following provisional proofs depend on given theorem `ACL2::G3`
from line 2 of each library. At `X = Y = 0` its formula asks for
`(o< 0 0)`. The remaining measure proofs in those inputs certify.

| Case under `checker/cases/` | Lines of `proofs.txt` |
| --- | --- |
| `provisional-walk-all` | 4–7 |
| `provisional-walk-default` | 4–7 |
| `provisional-walk-lambda` | 4–7 |
| `provisional-walk-lambda-repeats` | 4–7 |
| `provisional-walk-mbe` | 4–7 |
| `provisional-walk-mutual` | 7–10 and 11–14 |
| `provisional-walk-mutual-repeats` | 4–7 |
| `provisional-walk-nested` | 4–7 and 8–11 |

This command confirmed the counterinstance in ACL2 8.7 on 2026-11-24.

```sh
SBCL_USER_ARGS="--dynamic-space-size 1500" acl2 <<'EOF'
(thm (not (o< (acl2-count 0) (acl2-count 0))))
(good-bye)
EOF
```

### Other refused events

ACL2 also refused the definitions in `provisional-walk-default`,
`provisional-walk-mutual` and `provisional-walk-nested` with the available
termination premises. The cases are under `checker/cases/`.

The following events were also unavailable. Every proof in these cases
certifies.

| Case | Event and reason |
| --- | --- |
| `checker/cases/provisional-entry-define-skip` | The skipped local `BM-L2` recurses on the same argument with no base branch. |
| `checker/cases/provisional-library-proofs-partial` | The given `LOCAL-LOOP` recurses on the same argument with no base branch. The given constraint on `GIVEN-FN` requires an identity function, and the `nil` witness fails. |
| `checker/cases/provisional-library-proofs-skip-define` | The skipped local `LOCAL-LOOP` in the library's proofs recurses on the same argument with no base branch. |
| `checker-js/cases/library-proofs-define-skip` | The skipped local `C-LOCAL` in the library's proofs recurses on the same argument with no base branch. |
| `checker-js/cases/library-proofs-end-between-statements` | ACL2 refuses the new `COMMON-LISP::C-LEN` given at the end of the library's proofs. |
| `checker-js/cases/library-proofs-partial` | ACL2 refuses the new `COMMON-LISP::C-LEN`, whose two termination proofs certify. The given `C-GIVEN-REC` recurses on the same argument with no base branch. |
| `checker-js/cases/proof-local-skip` | The skipped local `C-LOCAL-REC` recurses on the same argument with no base branch. |
| `checker-js/cases/witness-large-arity` | The two constraints require written parameter lists for arities of at least 9,007,199,254,740,992. The witness proof's formula contains no call of a function in those signatures. |
