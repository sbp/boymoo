# Array scan

`lib` is the Library used by the B1 BookProof. Terms, Steps and Libraries
use the representations in `prover/sig/proof.md` and `prover/sig/library.md`.
Each exported proof recipe returns `(cons step lib)` with the auxiliary
facts and entries added in proof construction order. A recipe that cannot
give the pair returns a failure.

| Call | Result |
|---|---|
| `(b1-array-scan-valid-compressed-array lib formula)` | Proof of an `ARRAY1P` implication for the compressed array in `formula`, with the resulting Library. |
| `(b1-array-scan-read-compressed-array lib formula)` | Proof of an `AREF1` equality implication for the original and compressed arrays in `formula`, with the resulting Library. |

Substitution dictionaries use insertion order. The scan advance binding for
`I` precedes the accumulator binding when both are present. The list of
substitutions for reverse lookup has the advance-only substitution first.
