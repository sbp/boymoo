# Closed term computation

Terms, data, and Steps use the forms in `prover/sig/proof.md`. A package
table is an insertion-ordered alist from package-name strings to
`(imports hidden)` lists. Imports are symbol data in declaration order,
and `hidden` is a Boolean.

| ACL2 call | Arguments and result |
|---|---|
| `(h2-computation-tag value)` | The leading string tag of a compound datum, or `nil`. |
| `(h2-computation-integer-or-true-p value)` | Recognizes an integer or `t`. |
| `(h2-computation-rational value)` | The rational denoted by an integer or tagged ratio, or `nil`. The value `t` is interpreted as one here. |
| `(h2-computation-components value)` | The real and imaginary components as rational numbers, with zero defaults for nonnumeric atoms. |
| `(h2-computation-encode value)` | The integer or tagged ratio datum for a rational number. |
| `(h2-computation-number real imag)` | The encoded number datum for two rational components. |
| `(h2-computation-boolean value)` | The symbol datum for `NIL` on `nil`, `:none`, numeric zero, or an empty string, and for `T` on the other inputs. |
| `(h2-computation-contents value)` | The elements of a compound datum in list order, omitting a final dot record and its tail. |
| `(h2-computation-ascii-chars-p chars)` | Whether every character of the list is in the ASCII range. |
| `(h2-computation-primitive-value function args packages)` | The unquoted value for a primitive symbol, its ordered list of unquoted arguments, and the package table. |
| `(h2-computation-evaluate proof term packages fuel)` | `(cons step fuel)` with the Step for the closed term and the remaining rewriting budget. `proof` is a Search. `:none` or `nil` denotes an unlimited budget. A failure can occupy the Step position. |

Primitive evaluation can return `tactic-inapplicable` for an unusable
argument, missing package record, or a non-ASCII primitive name.
Unsupported primitive calls and hidden packages can return `unproved`.
The evaluator also returns `unproved` for a constrained function or
an exhausted rewriting budget and `fuel` when its recursion counter
runs out.

Evaluation uses the Search in `prover/h2/sig/search.md`. Completed closed
terms are stored in an alist with their Steps, so repeated occurrences
reuse them within the call.
