# Book proof recipes

Terms, Steps, Libraries, and proof entries have the forms in
`prover/sig/proof.md` and `prover/sig/library.md`. A Generator has the form
in `prover/t2/sig/tactics.md`. An event is a two-element list `(kind data)`,
where `kind` is the entry word as a string and `data` is its list of fields.
A source event is a three-element list `(raw kind data)`, where `raw` is the
original line including its terminator when present.

An Obligation is `(raw name kind data)` and a Candidate is
`(entries prerequisites)`. These are the list forms of their named
tuples. Entries preserve proof order. Dictionaries use association lists,
and new values for present keys retain the old positions.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t2-books-make-obligation raw name kind data)` | Obligation with the four given fields. | None. |
| `(t2-books-obligation-name target)` | Name of Obligation `target`. | None. |
| `(t2-books-obligation-kind target)` | Entry word of Obligation `target`. | None. |
| `(t2-books-obligation-data target)` | Entry fields of Obligation `target`. | None. |
| `(t2-books-first-name kind data)` | First function name in a definition or constraint, the name of a theorem, or `nil` for any other kind. | A failure from reading malformed fields. |
| `(t2-books-independent-theory lib)` | A Library with the same fields as `lib`, which subsequent calls can extend independently. | None. |

A StatementProver is `(:t2-books-statement-prover generator)`, whose field is its Generator. An optional Rules index is `nil` when omitted.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t2-books-statement-prover-init generator)` | StatementProver with Generator `generator`. | None. |
| `(t2-books-statement-prover-generator prover)` | Generator of StatementProver `prover` or BookProver `prover`. | None. |
| `(t2-books-statement-prover-generate prover target hints index)` | `(cons (list lib entry) prover)` with the Library and proof entry for Obligation `target` and the resulting StatementProver. `hints` is the name-to-hint dictionary and `index` is a Rules index or `nil`. | A failure from reading or proving the obligation. |
| `(t2-books-build-lemma-family lib family)` | Library after the one family identified by `family` from `*t2-books-book-lemmas*`. | A failure from building the lemmas. |

`*t2-books-book-lemmas*` is the list of family keywords in recipe order.
They are `:field`, `:order`, `:power`, `:power-products`, `:ratios`,
`:input-fields`, `:input-state`, `:input-channels`, `:exponent-parity`,
`:exponent-equalities`, `:dyadic`, `:rounding`, `:rational-scaling`,
`:half-parity`, `:quotient-rounding`, `:round-ties`, `:numeric-types`,
`:field-cancellation`, `:power-transport`, `:floor-bracket`,
`:floor-thresholds` and `:completed-operations`.

A BookProver is `(:t2-books-book-prover generator library library-measures
theory library-lines proofs skips)`. The first field is a Generator.
`library` is the original library source, `library-measures` is its
measure dictionary, and `theory` is the enriched Library. `library-lines`
is a list of distinct lines in first-occurrence order. `proofs` and `skips`
map statement source lines to Candidates and skip reasons, respectively.

| Call | Arguments and result | Failure |
|---|---|---|

File loading and output, external checkers, and command-line orchestration
are outside the books.

`(t2-books-parse-aid kind data measures hints)` processes a single event
with the supplied measure and hint dictionaries. It returns the resulting
`(measures hints)` or a failure from reading its fields.

`(t2-books-split-lines source keepends text-p)` splits a string into lines.
It retains each terminator if `keepends` is true. With `text-p` true it
recognizes the extended set of line terminators. The basic set
contains LF, CR, and CRLF.

`(t2-books-failure-kind-p value kinds)` tests whether `value` is a
failure whose kind is listed in `kinds`.

`(t2-books-statement-prover-generate-with-state prover target hints index)`
has the arguments and successful result of `generate`. On a failure, it
returns `(cons failure prover)` with the resulting prover so callers can
continue with the learned facts and lemma counter.

Candidate prerequisite keys use the serialized order returned by
`referenced-facts`. The lookup in `candidate` uses each key and clause,
and no proof text depends on the prerequisite dictionary's order.

`(t2-books-statement-prover-generate-with-prepared-rules prover target hints prepared)`
has the result of `generate-with-state` for a theorem or constraint.
`prepared` is the result of `t2-book-logic-rules-prepare` and is used
when the target reaches rule-based search. On a failure it returns
`(cons failure prover)` with the current prover.
