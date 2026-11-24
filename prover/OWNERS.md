# What each book is responsible for

The books of `prover/` in the order of `prover/ORDER`, in which they are certified. A book may use the books before it. `prover/sig/BOOK.md` gives the functions of a book with what they take and return, and `prover/notes/BOOK.md`, where a book has one, what else its user should know.

## The shared books

Every set of tactics stands on these (`prover/CONVENTIONS.md`).

| Book | Responsible for |
|---|---|
| `basics` | Text, sequences and tables, and the recognizer of failures. |
| `siphash` | The hash that gives a helper of a proof its name. |
| `reader` | Reading the lines of statements and proofs into data, and writing data as text. |
| `proof` | The Proof and the Step, the eight rules that make Steps, and the text of a proof. |
| `proof2` | The rules made of those eight: equalities, conditionals, cases, simplification and a small prover. |
| `library` | The Library: adding and citing lemmas, integer types, sums, and the first lemmas. |
| `library2` | The lemmas of order, length and size, and the build of the Library. |
| `termination` | The recursive calls of a definition and its obligations of termination. |
| `descent` | Hypotheses from the tests of a call, and the recipes for the measures that decrease. |

## The books of T1

| Book | Responsible for |
|---|---|
| `terms` | Term transformations. |
| `rulers` | Hypotheses from ruler tests. |
| `lemmas` | The slice library and its proof rules. |
| `book-library` | The book library and its proof rules. |
| `subtraction` | Subtraction and count descent. |
| `product-arithmetic` | Integer product proofs. |
| `ordinal-proofs` | Ordinal order proofs. |
| `selector-proofs` | Selector descent. |
| `countdowns` | Countdown descent. |
| `termination-proofs` | Proofs of termination obligations. |
| `witnesses` | Witness recipes. |
| `book-logic` | Reductions and induction instances. |
| `quotient-proofs` | Quotient descent. |
| `remainder-proofs` | Remainder bounds. |
| `shift-arithmetic` | Shift descent. |
| `halved-counters` | Halved counters. |
| `halving-proofs` | Length descent for a list splitter. |
| `lexicographic` | Ordinal construction and lexicographic descent. |
| `strsplit-proofs` | String split proofs. |
| `proper-lists` | Proper list recognizers. |
| `list-preservation` | List recognizer preservation. |
| `list-algebra` | List algebra. |
| `list-equivalence` | List equivalence proofs. |
| `finite-tables` | Finite case tables. |
| `fixer-proofs` | Type fixer invariance. |
| `evaluator-proofs` | Evaluator constraints. |
| `proof-search` | Fact lookup and proof search. |
| `constraint-proofs` | Constraint witnesses. |
| `book-proofs` | Book proof certificates. |
| `api` | Preparing an obligation, and the entry function `api-prove`. |
| `open` | Sessions, and the entry functions `api-open`, `api-prove-open` and `api-prove-all` (`prover/OPEN.md`). |
