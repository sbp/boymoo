# Hints

A hint, keyword argument, and substitution term use the frozen datum
representation of `prover/sig/proof.md`. A Library uses the representation
of `prover/sig/library.md`. These functions leave their arguments unchanged.

| Call | Result | Failure |
|---|---|---|
| `(t2-hints-arguments hint key)` | The list of data following the keyword with string name `key`, in generator order. | None on frozen data. |
| `(t2-hints-expanded-functions hint)` | The set of function heads selected by the expand hints. | None on frozen data. |
| `(t2-hints-enabled-functions hint)` | The set of function names enabled by the theory hints. | A failure for a missing `E/D` enable argument. |
| `(t2-hints-translate lib term)` | The translated ACL2 Core term, using the Library's defined and primitive operators. | `recipe-mismatch` for an unsupported application or `missing-term-part` for an empty application. |
| `(t2-hints-instances lib hints)` | The list of singleton-clause instance Steps, in hint order, including repeats. | A malformed outer instance can return a failure. A binding or proof that fails with `recipe-mismatch`, `missing-term-part` or an equivalent shared kind is skipped. |

Sets are lists of distinct members in the order of their printed sort keys.
