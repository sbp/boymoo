# Character lists for printing

`lib` is a Library as specified in `prover/sig/library.md`. Terms and Steps
have the forms in `prover/sig/proof.md`. `evidence` is a list of Steps in
the order supplied by the caller. Pass `nil` for omitted evidence.

The pair `(cons value lib)` carries the returned value and the Library
after the call, including any lemmas in their order of addition. A failure
from proof construction is returned directly.

| Call | Result |
|---|---|
| `(b1-printing-character-list lib term evidence)` | Pair with the Step proving that `term` is a character list. |
| `(b1-printing-pack-character-lists lib formula)` | Pair with the Step for the character-list invariant requested by `formula`, whose argument is a `PACK-LIST` or `PACK-TREE` call. |
| `(b1-printing-character-constant lib term)` | Step equating a `CHARACTERP` call on a quotation to its Boolean value, or `nil` if `term` does not have that form. |
| `(b1-printing-known-character lib value evidence)` | Pair with the Step proving `value` is a character. |
| `(b1-printing-proper-character-list lib known)` | Pair with the Step proving that the character list established by `known` is proper. |
| `(b1-printing-print-base-bound lib known)` | Two Steps in order, proving that the print base established by `known` is integral and above one. |
| `(b1-printing-floor-by-larger-base lib int-n pos-n int-base above-one)` | Pair with a two-element list of Steps. The first proves that the floor of `n` divided by `base` is below `n`, and the second proves the floor is natural. The input Steps establish that `n` is integral and positive and that `base` is integral and above one. |
| `(b1-printing-explode-integer-chars lib term accumulator-type)` | Pair with the Step proving that the integer printing call `term` gives a character list, given the Step `accumulator-type` for its accumulator. |
| `(b1-printing-printable-integer lib call integral)` | Pair with the Step proving that the `EXPLODE-ATOM` call on the integer established by `integral` gives a character list. |
| `(b1-printing-printable-rational lib call rational)` | Pair with the Step proving that the `EXPLODE-ATOM` call on the rational established by `rational` gives a character list. |
| `(b1-printing-explode-atom-chars lib call)` | Pair with the Step proving that `call`, an `EXPLODE-ATOM` term, gives a character list. |

The symbol constants are `*b1-printing-characterp*`, `*b1-printing-coerce*`,
`*b1-printing-realpart*`, `*b1-printing-imagpart*`, `*b1-printing-null*`,
`*b1-printing-characters*`, `*b1-printing-true-listp*`, `*b1-printing-digit*`,
`*b1-printing-print-base*`, `*b1-printing-explode-integer*`,
`*b1-printing-explode-atom*`, `*b1-printing-pack-list*`,
`*b1-printing-pack-tree*`, `*b1-printing-base*`, `*b1-printing-ans*` and
`*b1-printing-n*`.
