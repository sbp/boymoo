# Reader and writer

`prover/reader.lisp` reads the lines of statements and proofs into data, and writes data back as text. The text is the one of `spec/formats.md`: each datum has exactly one text, and the reader refuses any text that is not the one text of its datum. A source is an ACL2 string, and a code is the code of one of its characters.

## Data

| Datum | Example of its text | Form |
|---|---|---|
| Integer | `-12` | The integer. |
| Ratio | `3/4` | `("ratio" numerator denominator)`, in lowest terms with a denominator of 2 or more. |
| Complex rational | `#C(1 3/4)` | `("complex" real imaginary)`. Each part is an integer or a ratio, and the imaginary part is not 0. |
| Character | `#\41` | `("char" code)`. |
| String | `"abc"` | `("str" text)`. |
| Symbol | `ACL2::X` | `("sym" package name)`. |
| List | `(a b c)` | The list of the data of its members. It has at least one member. |
| Dotted list | `(a b . c)` | The list of the data of its members, with `("dot" tail)` as its last member. The tail is an atom other than the symbol `COMMON-LISP::NIL`. |

The first member of every form in the table but a list's is a string, the tag. A list of data never begins with a string, and that tells the two apart. The empty list is the symbol `COMMON-LISP::NIL` and is read and written so.

## The Reader

A Reader is `(:reader source index)`: the source and the position of the next character, from 0. A function that reads returns `(cons value reader)`, the value with the Reader moved past what was read. A failure (`prover/FAILURES.md`) takes the place of the pair.

| Function | Arguments and value | Failure |
|---|---|---|
| `(reader-reader source)`, `(reader-reader-init source)` | A Reader at position 0 of the source. | None. |
| `(reader-reader-s r)` | The source of the Reader. | None. |
| `(reader-reader-i r)` | The position of the Reader. | None. |
| `(reader-reader-peek r)` | The code at the position, or `-1` at the end of the source. | None. |
| `(reader-reader-take r text)` | The Reader moved past the string `text`. | `"value"` when `text` does not stand at the position. |
| `(reader-reader-escaped r close)` | The pair of a text and the Reader moved past the closing character, whose code is `close`. The Reader begins just after the opening character. In the text, `\` and two hexadecimal digits in upper case stand for the character of that code. | `"value"` when the source ends first, at a character outside the codes 32 to 126, at a `\` without two such digits after it, and at an escape of a character that is written as itself. |
| `(reader-reader-plain r)` | The pair of the longest run of plain characters at the position, which may be empty, and the Reader moved past it. | None. |
| `(reader-reader-part r)` | The pair of one part of a symbol and the Reader moved past it: the text between two bars when a bar stands at the position, and the run of plain characters otherwise. | `"value"` from the text between the bars, and when that text is not empty and has only plain characters. |
| `(reader-reader-rational r text)` | The integer or the ratio that the string `text` writes. `r` is not used. | `"value"` when `text` is not the one text of an integer or a ratio, and when a run of its digits is longer than 4,300. `"Fuel"` from the greatest common divisor. |
| `(reader-reader-datum r)` | The pair of the datum at the position and the Reader moved past it. | `"value"`, or `"Fuel"`. |
| `(reader-reader-line r)` | The pair of `(word arguments)` and the Reader moved to the end. The source from the position is one line, `(word argument ...)`: `word` is a string of lower-case letters and hyphens, each argument is a datum after one space, and the closing parenthesis is the last character of the source. | `"value"`, or `"Fuel"`. |

`"Fuel"` comes from three counters that begin at 1,000,000 (`prover/FAILURES.md`): `reader-reader-datum` takes one from its counter at each level of nesting and at each member of a list, `reader-reader-line` at each argument of the line, and the greatest common divisor at each of its steps.

## The writer

| Function | Arguments and value | Failure |
|---|---|---|
| `(reader-write x)` | The text of the datum `x`. | `"index"` when `x` is, or holds, the empty list `nil`. |
| `(reader-escape text close)` | The string `text` with the character of code `close`, `\`, and every character outside the codes 32 to 126 written as `\` and two hexadecimal digits in upper case. | None. |
| `(reader-part p)` | The string `p` as a part of a symbol: itself when it is not empty and has only plain characters, and otherwise between two bars, escaped with the bar as the closing character. | None. |
| `(reader-rat x)` | The text of an integer, or of a ratio in its form above. | None. |

## Constants

| Constant | Value |
|---|---|
| `*reader-plain*` | The list of the codes of the plain characters: the letters `A` to `Z`, the digits, and `-+*/<=>!?$%&_^~.@`. |
| `*reader-word-chars*` | The list of the codes of the characters of a line's word: the letters `a` to `z` and the hyphen. |
| `*reader-hex*` | The string of the sixteen hexadecimal digits, in upper case. |
| `*reader-decimal-limit*` | 4,300, the most digits that an integer, a numerator or a denominator may have. The sign is not counted. |
| `*reader-value-error*` | The failure `(:failure "value" "")` that the reader returns. |

## Cursors

Inside one call the reader works on a cursor, `(position . characters)`: a position in the source and the list of the characters from there on. The functions above make a cursor from their Reader, call the function of the same name on it, and make a Reader of the result. A book that reads many data from one source can stay on the cursor.

| Function | Arguments and value | Failure |
|---|---|---|
| `(reader-cursor r)` | The cursor at the position of the Reader. | None. |
| `(reader-at-cursor r cursor)` | The Reader of the source of `r` at the position of the cursor. | None. |
| `(reader-at-result r result)` | `(cons value reader)` for a result `(value . cursor)`. A failure is returned as it is. | None of its own. |
| `(reader-cursor-peek cursor)` | The code at the cursor, or `-1` at the end. | None. |
| `(reader-cursor-advance cursor count)` | The cursor `count` characters further on. | None. |
| `(reader-cursor-take cursor text)` | The cursor moved past the string `text`. | `"value"` when `text` does not stand there. |
| `(reader-cursor-escaped cursor close)`, `(reader-cursor-plain cursor)`, `(reader-cursor-part cursor)` | `(value . cursor)`, as the functions on a Reader of the same names. | As those. |
| `(reader-cursor-datum n cursor)` | `(datum . cursor)` for the datum at the cursor. `n` is the counter, and the caller at the top passes `1000000`. | `"value"`, or `"Fuel"`. |
| `(reader-prefix-p prefix chars)` | Whether the list of characters `chars` begins with the list `prefix`. | None. |
| `(reader-scan chars index alphabet reversed)` | `(text index . chars)` after the longest run of characters of `chars` whose codes are in the list `alphabet`: the run as a string, after the characters of `reversed` in reverse, then the position after the run when `index` is the position of the first character, and the characters left. | None. |
| `(reader-plain-code-p code)` | Whether the integer `code` is in `*reader-plain*`, found by comparing it with the ends of the runs of codes in that list. | None. |
| `(reader-scan-plain chars index reversed)` | What `(reader-scan chars index *reader-plain* reversed)` gives. | None. |
| `(reader-hex-byte chars)` | The number that the first two characters of the list write as hexadecimal digits in upper case, or `-1` when they do not. | None. |
| `(reader-all-digits-p chars)` | Whether every character of the list is a decimal digit. | None. |
| `(reader-decimal-value digits)` | The number that a list of decimal digits writes. | `"value"` for more than 4,300 digits. |
