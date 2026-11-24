# List folds and strings

`lib` is a Library. Steps and terms have the forms in `prover/sig/proof.md`.
The constants are `*t3-list-bounds-append*`, `*t3-list-bounds-char-list*`,
`*t3-list-bounds-character*`, `*t3-list-bounds-coerce*`,
`*t3-list-bounds-stringp*`, `*t3-list-bounds-list-type*`,
`*t3-list-bounds-string-type*`, `*t3-list-bounds-tail*`,
`*t3-list-bounds-cons-x*`, and `*t3-list-bounds-count-x*`.
The first five are function symbols, the next two are quoted type symbols,
and the last three are terms on `X`.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t3-list-bounds-define-fold lib name step base)` | The Library with a definition and measure proof for the unary function symbol `name`. Terms `step` and `base` are its cons and atom branches. | A failure from constructing or adding the definition and proof. |
| `(t3-list-bounds-tail-hypothesis lib formula cons)` | An induction-hypothesis Step for term `formula`, using a Step `cons` that establishes that `X` is a cons. | A failure from constructing the Step. |
| `(t3-list-bounds-tail-induction lib formula step base)` | An induction Step for `formula` given the cons and atom case Steps `step` and `base`. | A failure from constructing the Step. |
| `(t3-list-bounds-endp-branch lib call cons)` | A Step opening the empty-list test of term `call`, given a signed cons Step `cons`. | A failure from constructing the Step. |
| `(t3-list-bounds-append-branch lib left right cons)` | A Step opening append on terms `left` and `right`, given a signed cons Step `cons`. | A failure from constructing the Step. |
| `(t3-list-bounds-char-list-nil lib)` | A Step establishing that the empty list is a character list. | A failure from constructing the Step. |
| `(t3-list-bounds-char-list-components lib step cons)` | Two Steps for the character head and character-list tail, in that order, given the character-list Step `step` and cons Step `cons`. | A failure from constructing the Steps. |
| `(t3-list-bounds-char-cons lib head tail)` | A Step proving that adjoining the character established by Step `head` to the character list established by Step `tail` gives a character list. | A failure from constructing the Step. |
| `(t3-list-bounds-append-character-lists lib)` | The Library with a lemma that appending two character lists gives a character list. | A failure from constructing or adding the lemma. |
| `(t3-list-bounds-string-list-inverse lib characters)` | A Step equating the list coercion of a string coercion with the list proved to be a character list by `characters`. | A failure from constructing the Step. |
| `(t3-list-bounds-chars-to-string characters)` | The string coercion of term `characters`. | None. |
| `(t3-list-bounds-string-to-chars string)` | The list coercion of term `string`. | None. |
| `(t3-list-bounds-string-assertion lib characters)` | A Step establishing that the string coercion of term `characters` is a string. | A failure for a mismatched coercion fact or from constructing the Step. |
