# Countdown and index arithmetic

The symbol constants are `*h4-book-arithmetic-zp*`,
`*h4-book-arithmetic-natural-countdown-zero*`,
`*h4-book-arithmetic-natural-nonpositive-zero*` and
`*h4-book-arithmetic-index-in-bounds*`.

| Call | Result and failures |
|---|---|
| `(h4-book-arithmetic-predecessor value)` | The sum term with quoted negative one followed by the term `value`. |
| `(h4-book-arithmetic-countdown-lemmas p)` | The Library after adding the countdown and index entries in order. May return a failure. |
| `(h4-book-arithmetic-cancelled-predecessors p offset-left label)` | The Library with the cancellation lemma for the Boolean offset placement and string label. May return a failure. |
| `(h4-book-arithmetic-index-bounds p)` | The Library with the index bounds entries. May return a failure. |

The Library arguments and results use the shared Library form.
