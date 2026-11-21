# Checker guards

`check` has the guard `(and (stringp ground) (stringp library)
(stringp statements) (stringp proofs))`. ACL2 proves that under this
condition every call in the checker satisfies its callee's guard. With
the guard books included and guard checking enabled, ACL2 can execute
`check` and its callees in Common Lisp and obtain their logical values.
The reference runner evaluates the logical definitions in the exported
program.

The theorems concern safe ACL2 execution, including on malformed input
text. The correspondence with the Boymoo inference rules and proofs of
termination in Boymoo format belong to the review in [step 5 of the
plan](../../PLAN.md#5-review).

## Entry guards

The arguments not listed in the table can be arbitrary ACL2 objects.

| Function | Guard |
| --- | --- |
| `check` | Four strings holding the ground theory, library, statements and proofs. |
| `initial-world` | `t`. |
| `lines-of` | A string. |
| `lex-atom` | If there is a leading symbol part, its lookup in the package table is a true list. |
| `parse-loop` | A reader stack and a trie of package records. |
| `parse-line` | A trie of package records. |
| `ground-line` | A line satisfying `guard-ground-line-p` and a world satisfying `guard-world-p`. |
| `load-ground` | A world satisfying `guard-world-p`. |
| `admit` | A true list for the parsed line and a world satisfying `guard-world-p`. |
| `check-library` | A natural line number and a world satisfying `guard-world-p`. |
| `run` | Natural line numbers, a context satisfying `guard-proof-context-p` and a world satisfying `guard-world-p`. |
| `check-step` | A natural step count, a rational budget, a list satisfying `proof-clauses-p` and a world satisfying `guard-world-p`. |
| `prim-value` | A true list of arguments and a world satisfying `guard-world-p`. The values of the arguments can be arbitrary ACL2 objects. |
| `termination-obligations` | Definitions satisfying `defs-shape-p` and a true list of measures. |
| `witness-obligations` | `t`. |
| `verdict` | True lists for the world and its counts. |
| `rejection-verdict` | A true list for the rejection with a string in its input field. |

## Invariants

- `guard-trie-p` recognizes a trie with character keys, each paired with a
  child trie. A node's value is `NIL` for absence or a record of the kind
  stored in the trie. An import is held in a singleton list, which also
  represents an import of `NIL`. `guards-invariants.lisp` proves the
  shape of a lookup and preservation by `trie-put`, including what
  lookup gives at the updated key and at other keys.
- `guard-world-p` recognizes six fields. The package trie holds symbol
  imports, an import trie, a Boolean hidden flag and declaration lines.
  The name trie holds optional natural arities, optional facts and
  source lines. A stored fact has a true list of literals and a list of
  natural sizes of equal length. The remaining fields are the
  string-named facts, the specials trie, four natural counts and the
  ACL2 import trie. `guards-invariants.lisp` and
  `guards-admission-invariants.lisp` establish the initial shape and its
  preservation by ground-line processing, table updates, counting and
  admission. `guards-run-invariants.lisp` extends this to successful
  library and proof runs.
- `guard-reader-stack-p` recognizes a nonempty list of frames, each a
  true list of data. `guards-reader-stack.lisp` proves preservation
  when the reader opens a list, reads an element or closes a nested
  list, and proves that parsing yields a true list.
- `guard-pending-p` recognizes pending theorems, definitions, constraints
  and lemmas. `guard-proof-context-p` recognizes the pending entries and
  their continuations. A proof in progress carries a proper goal list,
  a list of prior clauses, a natural step count and an integer total
  size. A proof clause pairs a true list of literals with a proper list
  of sizes. An internal size can be an integer or `NIL`; the latter
  arises when pairing keys with fewer values. `guards-steps.lisp` and
  `guards-run-invariants.lisp` prove preservation by proof steps and
  by the transitions between pending entries and proofs.
- The termination walk carries a true list of controlling literals,
  a list of sizes and bindings from formals to sizes. Its context
  contains the table of formals and measures and the size of the
  current function's measure. `guards-termination.lisp` proves that
  recording calls and walking bodies preserve the list of sized
  clauses. The retained obligations carry their total sizes as
  well as their literals and individual sizes.

The recognizers used in guards are definitions in the six checker
books, in ACL2 Core. The proof books establish their properties and
certify the function guards separately from the export of the checker.

## Executable bodies

The table gives each function with a guard-specific body and its theorem in
`guards-equations.lisp` that states its logical equation. The `mbe`
expressions keep the logical operations and supply executable
alternatives. ACL2 proves the alternatives agree with the corresponding
logical expressions under the guards. The equation theorems for the
`mbe` cases hold for all ACL2 objects.

| Function | Guard requirement | Theorem |
| --- | --- | --- |
| `sum` | Treat an absent size as zero when adding sizes. | `cg-sum-logical-equation` |
| `calls-p` | Take total list projections of the lambda body and the logical branch of a `return-last` form. | `cg-calls-p-logical-equation` |
| `rename-calls` | Take total list projections of the formals and body of a lambda. | `cg-rename-calls-logical-equation` |
| `args-subst-size` | Treat a missing substitution size as zero in an argument sum. | `cg-args-subst-size-logical-equation` |
| `prim-value` | Evaluate primitives safely on their full logical domains. This covers arithmetic and comparisons, `car` and `cdr`, character conversions, `coerce`, and constructors and accessors for complex and rational numbers. | `cg-prim-value-logical-equation` |
| `step-substitute` | Treat an absent premise size as zero when adjusting the size after substitution. | `cg-step-substitute-logical-equation` |
| `step-beta` | Treat an absent substituted size as zero when computing the size of the beta conclusion. | `cg-step-beta-logical-equation` |
| `unquote-all` | Take total list projections through arbitrary quoted forms. | `cg-unquote-all-logical-equation` |
| `induct-sizes` | Treat absent substituted sizes as zero when computing the sizes of induction literals. | `cg-induct-sizes-logical-equation` |
| `first-name` | Take total list projections before the shape of a definition or constraint has been checked. | `cg-first-name-logical-equation` |
| `call-clause` | Treat an absent substituted measure size as zero when sizing the decrease literal. | `cg-call-clause-logical-equation` |
| `walk` | Take total projections through lambda, conditional and `return-last` forms. Treat an absent test size as zero in the size of the negated test. | `cg-walk-logical-equation` |
| `record` | Take total projections through lambda and `return-last` forms. | `cg-record-logical-equation` |
| `load-ground` | Check the shape of each parsed line before adding its data to the world. Return `:bad` when the shape check fails. | `cg-load-ground-on-success` |

The ground theory is fixed by [the specification](../../spec/logic.md#3-the-ground-theory).
The script evaluates the guard-safe loader on `spec/ground.txt` and
confirms that it produces a world of the required shape. The load
success theorem says that a successful load returns exactly the world
obtained by processing the parsed lines directly. With the other
logical equation theorems, this preserves the verdict on every
library, statement and proof string over the fixed ground theory.

## Runnable examples

`guards-counterexamples.lisp` proves the results below. The script also
runs the examples with guard checking enabled.

- A `compute` step on `(car '42)` yields `NIL` and proves
  `(equal (car '42) 'nil)`. ACL2's native `car` guard requires a cons
  or `NIL`. The executable alternative implements the total value
  required by [the primitive table](../../spec/language.md#3-the-primitive-functions).
- `(define COMMON-LISP::NIL 7)` yields `rejected statements 1`.
  Duplicate detection projects a first name before shape validation.
  The total projection of 7 yields `NIL`.
- The alternate ground text `(package 42 COMMON-LISP::NIL)` followed
  by a line feed yields `the ground theory could not be read`. A
  numeric name cannot be coerced to a character list within ACL2's
  execution guard. The four-string entry handles this case by
  checking the shape before loading the line.

## Running the checks

Run `sh checker/proofs/guards.sh --require-all` from the repository root.
The script certifies the guard books into `build/checker/acl2/` and
reads the annotations on the six checker certificates and each proof
certificate. It requires that skipped proofs, added axioms and trust
tags are absent. It compares the functions in ACL2's checker world
with the exported definitions. It checks the guard status of each
function in ACL2 and checks every call in the translated guards
against the primitives, ground functions and checker functions.
`checker/closed.py` checks the exported definition bodies. The script
also checks the declared four-string guard directly in the ACL2 world.

## Results

On 2026-11-21 under ACL2 8.7, `sh checker/proofs/guards.sh --require-all`
reported verified guards for all 217 checker functions. The certificate
annotation, ACL2 Core, entry guard and ground world checks passed. The
15 proof books have 2,339 lines and 90,849 bytes by `wc -lc
checker/proofs/guards*.lisp`. The audit took 20.7 seconds of elapsed time.
The export from `sh checker/build.sh` had 238 lines and 276,182 bytes by
`wc -lc build/checker/checker.statements`. `checker/skips.py` with an
empty library found 103 statements with obligations.

On the same date, `sh checker/test.sh` passed the 319 cases and
self-containment checks. ACL2 and the runner agreed on all 321 inputs.
Including `build/checker/acl2/guards-entry`, loading `checker/acl2-run.lsp`
and enabling guard checking also gave the runner's verdicts for all 321
entries in `build/checker/test/list`. `sh export/proofs/round-trip.sh`
passed with the round-trip books as written.

On 2026-11-21, `sh checks/agree.sh` completed in 23 minutes. Both
checkers accepted the example and gave the expected verdict on all
646 cases. They gave the same verdict on all 460 books, and the skip
generators produced identical proofs for each book.

## Timing the largest book

`sh export/run.sh std/strings/pretty` prepares the library and the book.
From the repository root, generate the 2,500 skips, time the runner, and
write one-case and six-case inputs for ACL2.

```sh
library=build/export/library.statements
statements=build/export/books/std/strings/pretty.statements
proofs=build/checker/pretty.proofs
mkdir -p build/checker
python3 -B checker/skips.py "$library" "$statements" > "$proofs"
time sh checker/check.sh "$library" "$statements" "$proofs"
printf 'pretty %s %s %s\n' "$library" "$statements" "$proofs" > build/checker/pretty.list
awk '{ for (i = 0; i < 6; i++) print }' build/checker/pretty.list > build/checker/pretty-six.list
time sh checker/acl2-check.sh < build/checker/pretty.list
time sh checker/acl2-check.sh < build/checker/pretty-six.list
```

The ACL2 estimate subtracts the elapsed time of one check from that of
six checks and divides by five. For the guard-enabled measurement,
certify with `sh checker/proofs/guards.sh --require-all` and use the
same `run-case` calls with this ACL2 prelude.

```lisp
(include-book "build/checker/acl2/guards-entry")
(ld "checker/acl2-run.lsp")
(set-guard-checking t)
```

On 2026-11-21, the library had 4,151 lines and 3,077,290 bytes and
`std/strings/pretty` had 3,918 lines and 2,324,057 bytes by `wc -lc`.
The skip file had 2,500 lines and 107,726 bytes. The median elapsed time
of three runner shell invocations was 7.435 seconds. Each invocation
gave `provisional skipped 2500 assumed 0 given-definitions 502 given-facts 371`.

| ACL2 invocation | One case | Six cases | Seconds per check after subtracting startup |
| --- | ---: | ---: | ---: |
| `checker/acl2-check.sh` | 1.395 s | 7.308 s | 1.183 |
| With the guard certificate and guard checking enabled | 1.370 s | 5.671 s | 0.860 |

## Unverified functions

None.
