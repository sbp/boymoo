# L1 certificate interface

`(l1-api-prove statement earlier library aids)` takes a statement string and three lists of input strings. It returns `(lemmas entry)` when it constructs a certificate and `nil` otherwise. `lemmas` is a list of helper entry strings in certificate order and `entry` is the statement's entry string. The strings include their line terminators.

`*l1-api-prefix*` is `"L1"`. `*l1-api-symbol-prefix*` is `"ACL2::PROVER-L1-"`. Names and aliases in certificate text are serialized strings. The Proof and choice use the constructors and accessors of their owning books.

| ACL2 function | Arguments and result | Failure |
|---|---|---|
| `(l1-api-parse line)` | Reads a byte string and returns `(kind fields)` with the parsed fields in prover term form. | Malformed input. |
| `(l1-api-raw line)` | Removes every trailing LF from an ASCII string. | Input outside the ASCII string format. |
| `(l1-api-extend proof choices seen rows)` | Admits the strings in `rows` into the WarrantProof. Returns `(proof choices seen)` with the resulting Proof, choices in admission order, and set of raw row strings. | A failure from reading or admitting a row. |
| `(l1-api-library rows)` | Admits a list of strings into a fresh WarrantProof. Returns `(proof choices seen)` as in `l1-api-extend`. | A failure from initializing the Proof or admitting a row. |
| `(l1-api-context-names rows)` | Returns the sorted set of helper names occurring outside quoted strings and escaped symbol parts in `rows`. | A failure from reading a row. |
| `(l1-api-namespace-replace text names)` | Applies aliases to the certificate byte string `text`. `names` is an insertion-ordered alist from original token strings to replacement strings. | None. |
| `(l1-api-namespace source context)` | Gives the helpers in the certificate source names derived from their text and returns `(lemmas entry)`. The source is a byte string or a list of byte strings that end between entries and keep a definition with its measure or its local choice. `context` is a list of input strings. | Invalid entry structure, invalid or colliding helper names, or a failure from reading or writing the entry. |

Every input line represents one statement or proof header. `library` is admitted before `earlier`. The raw row set is used for membership and contains each row once. A measure in `aids` is used only for a definition. Stored measures use an insertion-ordered alist in which the last measure for a name supplies its value.

Sets of strings are lists ordered by the text of their ACL2 string literals.

| ACL2 function | Arguments and result | Failure |
|---|---|---|
| `(l1-api-parsed-obligation raw parsed)` | Takes the raw statement and its parsed `(kind fields)`. Returns `(raw kind fields name calls)` for a supported obligation or `nil`. | A failure from inspecting a statement. |
| `(l1-api-context-sources proof choices obligation aids)` | Takes the admitted Proof, choices in admission order, a supported obligation, and the aid lines. Returns the list of certificate source strings or `nil`. The caller checks whether the statement is already present. | A failure from reading aids or generating the certificate. |
| `(l1-api-obligation-sources proof choices obligation stored preparation)` | As in `l1-api-context-sources`, with stored measures from `l1-api-aid-measures` and the preparation described by `l1-books-generate-prepared`. | A failure from generating the certificate. |

For a constraint, the certificate search can introduce a local choice for
a comparison after the witness and warrant tactics leave it unproved.
