# Prover data and assembly

The constants `*prove-sets*`, `*prove-order*`, `*prove-library-order*`,
`*prove-entry-word*`, `*prove-aid-words*`, and `*prove-warrant*` hold,
respectively, the set names, the two kind-to-order alists, the kind-to-entry
word alist, the aid line openings, and the warrant text used to prefer a
tactic set. Their keys and names are strings.

A statement has the form in `prover/driver/sig/worklist.md`. An entry is
`(:entry number name blocks failure)`. `number` is the one-based input line
number, `name` the printed obligation name, and `blocks` is either `nil` or
a nonempty list of ASCII block strings in helper order followed by the main
block. `failure` is a diagnostic string, empty when there is no failure.
A target is `(:target entry statement line aids order)`. `entry` is its
entry, `statement` the parsed statement, `line` the original line, `aids`
the relevant aid lines in input order, and `order` the list of `(set-name
seconds)` pairs. A row is `(line statement target)`. Its target is `nil`
when the line has no selected target. An aid index is `(:aids index)`,
where `index` associates each printed name with the list of its `(index
line)` pairs. Each pair uses the zero-based position in the original aid
lines. Both the keys and their rows are kept in first-occurrence order.

Options are `(:options sets library-order tactic-seconds)`. `sets` is
`:none` for automatic order or a list of set names, including `nil` for an
explicit empty list. `library-order` is a Boolean. `tactic-seconds` is a
rational override, or `nil` for the default. Zero also uses the default.
`selected` is `:none` to select every eligible statement, or a list of
one-based statement numbers, including `nil` to select none.

| Function | Arguments and result |
|---|---|
| `(prove-entry number name blocks failure)` | Constructs an entry from the four fields above. |
| `(prove-entry-number entry)` | The input line number of `entry`. |
| `(prove-entry-name entry)` | The printed obligation name of `entry`. |
| `(prove-entry-blocks entry)` | The certificate blocks of `entry`, or `nil`. |
| `(prove-entry-failure entry)` | The diagnostic string of `entry`. |
| `(prove-entry-with-blocks entry blocks)` | A copy of `entry` with certificate `blocks` as above. |
| `(prove-target entry statement line aids order)` | Constructs a target from the five fields above. |
| `(prove-target-entry target)` | The entry of `target`. |
| `(prove-target-statement target)` | The parsed statement of `target`. |
| `(prove-target-line target)` | The original line of `target`. |
| `(prove-target-aids target)` | The relevant aid lines of `target`. |
| `(prove-target-order target)` | The ordered tactic attempts of `target`, with seconds. |
| `(prove-target-pending target)` | `t` if the target's entry has no certificate and its failure string is empty, or `nil`. |
| `(prove-row line statement target)` | Constructs a row from the three fields above. |
| `(prove-row-line row)` | The original line of `row`. |
| `(prove-row-statement row)` | The parsed statement of `row`. |
| `(prove-row-target row)` | The target of `row`, or `nil`. |
| `(prove-options sets library-order tactic-seconds)` | Constructs options from the three fields above. |
| `(prove-options-sets options)` | The explicit list of sets in `options`, or `:none`. |
| `(prove-options-library-order options)` | The library order flag in `options`. |
| `(prove-options-tactic-seconds options)` | The tactic time override in `options`, or `nil`. |
| `(prove-aids lines)` | Builds the aid index from the list of ASCII aid `lines`. It skips aid lines whose opening name cannot be read and printed. |
| `(prove-aids-rows aids)` | The alist of names and their indexed aid lines in `aids`. |
| `(prove-aids-for-statement aids statement)` | The list of relevant aid lines in `aids` for `statement`, in original input order. A definition group uses every defined name. Other kinds use their obligation. |

The aid index skips lines whose name cannot be read and propagates a
`fuel` failure from the reader.

A prefix contains the statement lines preceding a target, stored in reverse
order as `(:prefix reversed-lines)` so adding one line takes constant time.

| Function | Arguments and result |
|---|---|
| `(prove-prefix)` | An empty prefix. |
| `(prove-prefix-add prefix line statement)` | A prefix with `line` appended to `prefix`. `statement` is the parsed record for the line. |
| `(prove-prefix-lines prefix)` | The lines of `prefix` in input order. |
| `(prove-valid-blocks answer statement)` | `answer` is `nil` or the pair `(support entry-text)`, with `support` a list of blocks beginning with `define`, `lemma` or `choose` entries. Returns the nonempty list of valid blocks in helper order followed by the main block, or `nil`. An answer for an unknown statement kind gives the generic failure. |
| `(prove-prover-order options statement line)` | Takes the options, parsed statement, and original line. Returns ordered `(set-name seconds)` pairs. An unknown kind with automatic order or a constraint without a witness obligation gives the generic failure. |
| `(prove-prover-run options library statements aids selected)` | Takes options, the library and statement line lists, an aid index, and the selection above. Returns `(rows entries targets)` in input order. Byte-for-byte repeats of library or earlier statement lines are omitted. Protected obligations and obligations outside the selection have entries only. It propagates a failure from reading a statement or determining tactic order. |
| `(prove-prover-assemble entries all-skips)` | Takes the entries in order and an `all-skips` Boolean. Returns `(text ends)`, the assembled ASCII proof file and the cumulative count of line feeds after each entry. |
| `(prove-provisional verdict)` | Returns `(skipped-digits)` for a provisional verdict, or `nil`. The digits are the original string. |
| `(prove-rejected verdict)` | Returns `(file location-digits)` for a rejection verdict, or `nil`. The file is `"library"`, `"statements"`, or `"proofs"` and the digits are the original string. |
| `(prove-skip-count verdict)` | Returns zero for `accepted`, the integer skip count for a provisional verdict, or `nil`. A decimal conversion failure gives the generic failure. |
| `(prove-prover-checked entries ends numbers verdict)` | Chooses the zero-based index of an entry whose certificate should be dropped. `entries` are in input order, `ends` are the aligned cumulative proof line counts, `numbers` are the aligned input statement numbers, and `verdict` is the ASCII verdict line or `nil` for an unclassified checker result. Returns `nil` if the verdict confirms the skip count. A library rejection, an unconfirmed verdict with no certificate to remove, or a decimal conversion failure gives the generic failure. |
| `(prove-prover-checked-halve entries)` | Takes entries in input order and returns the zero-based positions to drop in descending certificate size, using input order for ties. Drops continue until at most half the total encoded byte size remains. |

`(cache-subset-dependencies blocks statement names packages)` takes the
certificate block strings, the statement line, and two alists supplied by
the cache. `names` maps printed qualified names to declaration digests.
`packages` maps printed package parts to lists of declaration digests. A
digest is a string whose character codes are the encoded digest bytes.
The function returns one such string with all distinct dependency digests
concatenated in byte order, or a `fuel` failure if the scan exhausts fuel.
