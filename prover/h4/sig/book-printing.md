# Character-list proofs for printing and packing

`p` is the H4 Tactics library. Terms and Steps use the representations in `prover/sig/proof.md`. `premises` is an ordered list of evidence Steps. Pass `nil` for an empty list. `support` is an alist of fact names and their clauses. A failure replaces the whole result.

| Call | Result | Failure |
|---|---|---|
| `(h4-book-printing-unfold p call premises)` | Step for the definition of `call` with its right side normalized using `premises`. | A failure from proof construction. |
| `(h4-book-printing-quoted-character p term)` | Step that the given character quotation satisfies `CHARACTERP`. | A failure from an invalid quotation or proof construction. |
| `(h4-book-printing-character-of p term premises)` | Step that `term` satisfies `CHARACTERP`, using the first matching premise if present. | A failure from proof construction. |
| `(h4-book-printing-characters-of p term premises)` | Step that `term` satisfies `CHARACTER-LISTP`, using the first matching premise if present. | A failure from proof construction or a missing rule. |
| `(h4-book-printing-character-results p equation premises)` | Step that the left side of the equality Step `equation` satisfies `CHARACTER-LISTP`. | A failure from proof construction. |
| `(h4-book-printing-character-lemmas p)` | Library extended with the cons, true-list and digit lemmas. | A failure from proof construction. |
| `(h4-book-printing-decimal-digits p)` | Library extended with the lemma for decimal digits. | A failure from proof construction. |
| `(h4-book-printing-decimal-atom p)` | Library extended with the lemmas for printing decimal integers, rationals and atoms. | A failure from proof construction. |
| `(h4-book-printing-printing-support p)` | `(cons support p-new)` with the updated library and its new facts, in the order in which they were added (`prover/h4/notes/book-printing.md`). | A failure from proof construction. |
| `(h4-book-printing-packing-formula formula)` | Boolean recognizing the character-list assertion for a unary `PACK-LIST` or `PACK-TREE` application to an atomic argument. | A failure from reading a malformed formula. |
| `(h4-book-printing-packing-proof p formula support)` | `(cons step p-new)` with a proof of `formula` and the library after installing `support`. If the tactic is inapplicable, the result is `(cons nil p)`. | A failure from matching or proof construction. |

The book's constants have the prefix `*h4-book-printing-` and a final `*`.
The names are `character`, `coerce`, `list`, `mod`, `rational`,
`characters`, `true-list`, `append`, `member`, `digit`, `explode-int`,
`explode-atom`, `print-base`, `pack-list`, `pack-tree`, `ten`, `logic`,
`character-cons`, `character-true-list`, `digit-character`,
`decimal-digits`, `decimal-integer`, `decimal-rational` and `decimal-atom`.
