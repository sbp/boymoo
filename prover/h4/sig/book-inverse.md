# Ordinal conversion inversion

`p` is the Library used for the book tactics. Terms and Steps follow
`prover/sig/proof.md`. `expansions` is the ExpansionProofs object from
`prover/h4/sig/book-expansion.md`, and `support` is a fact alist in
insertion order. Each entry is `(name . clause)`.

`*h4-book-inverse-atoc-type*`, `*h4-book-inverse-ctoa-type*` and
`*h4-book-inverse-inverse-conversion*` are the names of the two
conversion type facts and the expansion-after-compression lemma.

| ACL2 call | Result |
|---|---|
| `(h4-book-inverse-compression-type p e0-ordinal)` | Step proving that `ATOC` of the argument typed by `e0-ordinal` is an ordinal. |
| `(h4-book-inverse-converted-constructor p term continuing)` | Equality Step expanding the converted ordinal constructor `term`, using the active-count Step `continuing`. |
| `(h4-book-inverse-nonzero-inverse p identity original)` | Nonzero Step for the compressed exponent in `identity`, from the original nonzero Step `original`. |
| `(h4-book-inverse-expansion-of-sum p exponent-type right-type nonzero exp-identity suffix-identity sorted-tail order)` | Equality Step expanding the sum of a single exponent and an ordinal suffix, from their type, nonzero, inverse, sortedness and order Steps. |
| `(h4-book-inverse-expansion-inverts-compression p order)` | Induction Step proving that expansion inverts compression, given the expansion order Step. |
| `(h4-book-inverse-expansion-injective p expansions left-type right-type equality)` | Equality Step for the ordinals typed by `left-type` and `right-type`, given the equality of their expansions. |
| `(h4-book-inverse-atom-expansion p formula subject)` | Step for the finite-expansion formula on `subject`. |
| `(h4-book-inverse-inverse-shape formula)` | `nil` or `(mode . subjects)`. The mode is one of `"expansion after compression"`, `"compression after expansion"`, `"finite expansion"`, `"compression order"`, `"expansion equality"` or `"compression equality"`. Subjects follow in formula order. |

An InversionProofs object has form `(:h4-book-inverse-inversion-proofs
expansions inverse)`. `inverse` is the named auxiliary fact Step or
`nil` when it has yet to be prepared. Use the accessors to read its fields.

| ACL2 call | Result |
|---|---|
| `(h4-book-inverse-inversion-proofs-init expansions)` | InversionProofs with the given ExpansionProofs object and an empty inverse field. |
| `(h4-book-inverse-inversion-proofs-expansions self)` | The ExpansionProofs object in `self`. |
| `(h4-book-inverse-inversion-proofs-inverse self)` | The inverse Step or `nil`. |
| `(h4-book-inverse-inversion-proofs-with-expansions self expansions)` | `self` with the caller's current copy of the shared ExpansionProofs object. |
| `(h4-book-inverse-inversion-proofs-prepare self p)` | `(list self p)` with the updated objects. |
| `(h4-book-inverse-inversion-proofs-apply self p proof)` | Instantiated inverse Step discharged with the premise Step `proof`. |
| `(h4-book-inverse-inversion-proofs-from-compressed-equality self p equality left-type right-type)` | Equality Step for the original ordinals, given their type Steps and the equality of their compressions. |
| `(h4-book-inverse-inversion-proofs-prove self p formula support)` | `(list step self p)` with a Step or `nil` in the first field and the resulting objects in the second and third. The returned Library includes auxiliary entries and restores the input fact alist after a support-scoped proof. |

When a caller also holds the ExpansionProofs object separately, supply
its current value with `with-expansions` before a proof and obtain its
resulting value from the returned InversionProofs object. This preserves
the sharing of the two objects.
Proof operations can return a failure in place of their entire result.
The shape matcher can return a failure for
malformed terms.

`(h4-book-inverse-conversion-equality p formula evidence invert)`
returns the equality Step under the implication in `formula`, or a
failure. The evidence contains the two type Steps, in operand order.
Pass `(list :expansion expansions)` to reflect equality through
expansion or `(list :compression self)` to reflect it through
compression with a prepared InversionProofs object.
