# Scan bounds

`proof` is an H1 Prover. Terms and Steps have the forms in
`prover/sig/proof.md`. A list of signed tests has ordered `(term holds)`
pairs with `t` for true and `nil` for false.

| Call | Result | Failure |
|---|---|---|
| `(h1-book-scan-scan-induction proof call template measure prove-leaf)` | The induction Step for an application term `call`, a claim `template` with the result slot, and the ordinal `measure` term. | A failure from proof construction or a leaf. |
| `(h1-book-scan-weak-reflexive proof term)` | A Step for `term <= term`. | A failure from proof construction. |
| `(h1-book-scan-bound-across proof start middle end left right integer-facts)` | A weak bound Step from `start` to `end`, given the Steps `left` and `right` and an ordered list of integer evidence Steps. | A failure from proof construction. |
| `(h1-book-scan-previous-natural proof current previous typed sign)` | A Step that the term `previous` is natural, given the term `current` and its integer and sign Steps. | A failure from proof construction. |
| `(h1-book-scan-install-before-bounds proof)` | The Prover with the backward newline scan bound installed. | A failure from proof construction. |
| `(h1-book-scan-install-after-bounds proof)` | The Prover with the forward newline scan bounds installed in order. | A failure from proof construction. |
| `(h1-book-scan-install-diff-bounds proof)` | The Prover with the recursive first-difference bound installed. | A failure from proof construction. |
| `(h1-book-scan-install-diff-wrapper proof)` | The Prover with the first-difference wrapper bound installed. | A failure from proof construction. |

`prove-leaf` is `:before`, `:after`, or `:diff` for the three scan recipes.
It can also be an association list from each request
`(value actual tests hypothesis changes)` to its Step or failure. `value`
is a result term, `actual` is the instantiated claim, and `hypothesis`
is the induction Step for a recursive result or `nil` for another result.
`changes` is the dictionary of changed parameters in formal parameter order.
Distinct recursive binding lists are retained for induction in order of
first occurrence in the result tree. True branches precede false branches.

The constants `*h1-book-scan-before*`, `*h1-book-scan-after*`,
`*h1-book-scan-diff-recursion*`, `*h1-book-scan-diff*`,
`*h1-book-scan-length*` and `*h1-book-scan-end*` are `NEWLINE-BEFORE`,
`NEWLINE-AFTER`, `FIRST-DIFF-POSITION-REC`, `FIRST-DIFF-POSITION`,
`COMMON-LISP::LENGTH` and `END` in prover form.

`(h1-book-scan-scan-induction-leaf value tests proof call template measure prove-leaf formula substitutions)`
returns `(cons step substitutions)` for the given leaf, or a failure. The
`substitutions` dictionary maps each binding list to `nil`. It retains the
first position of an existing binding list.

| Branch proof function | Result |
|---|---|
| `(h1-book-scan-install-before-bounds-leaf value claim tests induction changes proof premise)` | A Step for the backward scan leaf's natural result and upper bound. |
| `(h1-book-scan-install-after-bounds-leaf value claim tests induction changes proof nat-end allowed successor)` | A Step for the forward scan leaf's natural result and interval. |
| `(h1-book-scan-install-diff-bounds-leaf value claim tests induction changes proof premise ends)` | A Step for the first-difference leaf's interval. `ends` is the list of the two length terms in order. |
| `(h1-book-scan-install-diff-wrapper-leaf value tests proof)` | A Step proving the selected length value natural. |

Each branch proof function can return a failure. `claim`, `premise`, `nat-end`,
`allowed`, `successor`, and `value` are terms. `induction` is the Step for
the recursive branch or `nil` for a nonrecursive branch. `changes` is an
insertion-ordered dictionary from formals to their changed actuals.
