# Reader and writer

The signatures are in `prover/sig/reader.md`.

The reader holds to the rule of `spec/formats.md` that a datum has one text. It refuses a number with a leading zero, `-0`, a ratio that is not in lowest terms or whose denominator is below 2, a complex rational whose imaginary part is 0, an escape of a character that is written as itself, bars around a part that needs none, a dotted tail that is a list or `COMMON-LISP::NIL`, and `()`. A line must end with its closing parenthesis, with no line feed after it: `run-parse-line` of `prover/book-proofs.lisp` gives the reader one line without its end.

A Reader is the source and a position, and stays a plain value that a caller can keep. Each function on a Reader makes the list of the source's characters from the position on once (`reader-cursor`), reads from that list, and returns a Reader at the new position. `reader-reader-line` reads all its arguments on one cursor.

The reader recurs with counters, since a datum can be nested to any depth; the writer recurs on the datum itself and needs none. The count of 1,000,000 bounds the nesting and the number of members of one list together.

An integer, a numerator or a denominator of more than 4,300 digits is refused with the kind `"value"`. The limit is `*reader-decimal-limit*`.

`reader-reader-rational` takes a Reader and does not use it.
