# Finite case tables

A term, a Step, and a Library have the forms specified in `proof.md` and `library.md`. A case is a pair `(test holds)`, where `holds` is `t` or `nil`. `known` is an alist from terms to Steps in insertion order. `proved` is an alist from quoted constants to Steps, and `upper` or `boundary` is a Step proving a strict upper bound.

| ACL2 call | Result |
|---|---|
| `(finite-tables-table-values term)` | List of the quoted leaf values in branch order, including repeats. |
| `(finite-tables-available-bound lib value known)` | `(cons step lib)` for the tightest available strict bound on `value`, with `nil` when no such bound is found. The Library can gain a remainder lemma. |
| `(finite-tables-impossible-value lib goal cases upper)` | Step proving `goal` from a case that contradicts `upper`. |
| `(finite-tables-finite-table-predicate-leaf constant cases lib predicate proved boundary)` | The proved Step for a constant, or a Step excluding its case by the boundary. |
| `(finite-tables-finite-table-predicate lib goal known)` | `(cons step lib)`, where `step` proves `goal` or is `nil` if the tactic found no proof. The Library can gain the table lemma and a lemma providing the bound. |

Every function can return a failure. The branch traversal and the range
check return `unproved` for a nonliteral leaf and for a bound that
does not suffice, respectively.

The two results that carry a Library put a failure in the Step position, preserving the Library reached by the call.
