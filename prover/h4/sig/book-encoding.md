# Book proof serialization

The Step and datum forms are those of the shared Proof books.
Each result may be replaced by a failure from writing a datum.

| Call | Result |
|---|---|
| `(h4-book-encoding-proof-lines last)` | The byte strings for the Step `last` and its dependencies. A left-to-right traversal emits the dependencies before their consumer. Duplicate lines take the number of their first occurrence, beginning with one. Each line includes its newline. |
| `(h4-book-encoding-book-entry kind name arguments proofs)` | A two-element list of the total step count and the entry source byte string. The header contains the kind string, name and argument list. The proofs are Steps serialized in order, with fresh numbering and a final `qed` line for each proof. |

A rule word or entry kind outside ASCII produces a failure.
