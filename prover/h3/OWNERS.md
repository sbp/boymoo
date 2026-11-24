# H3 book responsibilities

The books load in the order listed in `ORDER`. The shared books define
the representation of terms, proof steps, declarations, and libraries.

| Books | Responsibility |
|---|---|
| `induction`, `rewrite` | Construct induction cases and reduce or prove terms by rewriting. |
| `book-witness`, `book-descent` | Choose constraint witnesses and prove termination measures. |
| `lexicographic`, `numeric`, `state`, `symbolic-order` | Prove facts about lexicographic and symbol order, numeric types, and state fields. |
| `lists`, `merges`, `sorting` | Prove list properties, merge and sort types, and the corresponding decreases. |
| `counts`, `ancestors`, `atom-order`, `event-counts` | Prove count, ancestor-checking, and atomic-order properties. |
| `book-arithmetic`, `book-sums`, `numeric-order` | Normalize arithmetic and prove additive and numeric-order comparisons. |
| `book-signs`, `book-quotient`, `book-numerator`, `book-order` | Prove signs, ratios, and bounds. |
| `book-floor`, `book-rounding`, `book-mod`, `book-translation`, `book-parity`, `book-mod-interval` | Prove results about division, rounding, remainders, and parity. |
| `book-powers`, `book-exponent`, `book-power-order`, `book-power-identities`, `book-power-products` | Establish power types, bounds, and identities. |
| `tactics`, `book-tactics` | Select theorem recipes and dispatch proof obligations. |
| `generate`, `books` | Admit declarations, collect dependencies, and assemble proof text. |
| `api`, `open` | Publish proof entries and maintain sessions. |

Signatures and implementation notes describe the inputs and results of
the books. See [signatures](sig/) and [notes](notes/).
