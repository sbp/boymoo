# Primitive application and badge certificates

Proofs, Steps, symbols, and terms have the forms in `prover/sig/proof.md`.
The constants are `*l1-primitive-apply-prim*`, `*l1-primitive-hons-get*`,
`*l1-primitive-hons-assoc*`, `*l1-primitive-hons-equal*`,
`*l1-primitive-eql*`, `*l1-primitive-key*`, `*l1-primitive-arguments*`,
`*l1-primitive-block-size*`, `*l1-primitive-dispatch-block*`, and
`*l1-primitive-alist-entry*`. Their values are prover symbols or integers.

| Function | Arguments in order | Result | Failure |
| --- | --- | --- | --- |
| `l1-primitive-cons-list` | Value term list, tail term | Nested `CONS` term. Pass `*proof-false*` for the default tail. | None |
| `l1-primitive-arm-variable` | Index integer | Symbol for the arm at that index | None |
| `l1-primitive-false-prefix` | Proof, positive length, length-to-Step cache | `(cons step cache)` for the false prefix, with the resulting cache | Proof or fuel failure |
| `l1-primitive-skip-branches` | Proof, list of `(test arm)` pairs, tail term, list of definition symbols | Equality Step eliminating the initial false branches and selecting the next branch | Proof or assertion failure |
| `l1-primitive-dispatch` | Proof, function symbol, arity integer | `(variables step)` with the argument symbols and the dispatch equality Step | Proof, assertion, or fuel failure |
| `l1-primitive-discharge-primitives` | Certificates, Step, optional user badge test term | `(cons step certificates)` with the discharged Step and the updated Certificates. Pass `nil` for an absent badge test. | Proof, assertion, key, or fuel failure |

## Certificates

A Certificates object is `(:l1-primitive-certificates proof entries)`. The
entries are `(name count source)` records in the order added. `count` is
the number of proof steps and `source` is the entry text, as an ACL2 string.
Use the accessors and replacement function below to read and update it.

| Function | Arguments in order | Result | Failure |
| --- | --- | --- | --- |
| `l1-primitive-certificates-init` | Proof | Certificates with the given Proof and empty entries | None |
| `l1-primitive-certificates-proof` | Certificates | Current Proof | None |
| `l1-primitive-certificates-entries` | Certificates | Current list of entry records | None |
| `l1-primitive-certificates-with-proof` | Certificates, replacement Proof | Certificates with the given Proof and the existing entries | None |
| `l1-primitive-certificates-add` | Certificates, entry name symbol, Step | `(cons fact-step certificates)` with the cited fact and the updated Certificates | Proof or assertion failure |
| `l1-primitive-certificates-close` | Certificates | Certificates with the scoped facts deleted from the Proof | `MissingWarrantDependency` when a scoped fact is absent |

## BadgeTable

A BadgeTable is `(:l1-primitive-badge-table certificates table row-text
starts blocks queries)`. It uses the current Proof of its Certificates.
`table` is the list of rows in definition order, `row-text` is their
space-separated proof text, and `starts` holds their offsets in that text.
`blocks` is an alist from the starting index to `(end name)` in insertion
order. `queries` is the number of lookup certificates already added.

A quoted table tail uses its row list as term data. The record that carries the row list, cached text, and starting offset is `(:l1-primitive-table-tail rows text start)`.

| Function | Arguments in order | Result | Failure |
| --- | --- | --- | --- |
| `l1-primitive-table-tail-new` | Row list, byte string, starting index | TableTail object | None |
| `l1-primitive-table-tail-proof-text` | TableTail | Parenthesized text from the starting index | None |
| `l1-primitive-badge-table-init` | Certificates | BadgeTable for the primitive badge definition | Proof, assertion, or key failure |
| `l1-primitive-badge-table-certificates` | BadgeTable | Current Certificates | None |
| `l1-primitive-badge-table-quoted-tail` | BadgeTable, table index | Quoted row list. Negative indices count from the end. The row count selects `*proof-false*`. | An index outside the supported range |
| `l1-primitive-badge-table-entry-equation` | BadgeTable | BadgeTable with the association-list entry certificate added | Proof or assertion failure |
| `l1-primitive-badge-table-block` | BadgeTable, start index, end index | BadgeTable with the block and its certificate added | Proof or assertion failure |
| `l1-primitive-badge-table-lookup` | BadgeTable, function symbol | `(cons step table)` with the lookup equality Step and the resulting BadgeTable | Proof, assertion, or fuel failure |
| `l1-primitive-badge-table-witnesses` | BadgeTable, function symbol | `(cons (list member badge) table)` with the membership Step, the badge equality Step or `nil`, and the resulting BadgeTable | Proof, assertion, or fuel failure |
| `l1-primitive-discharge-primitives-find-badge` | Function symbol, BadgeTable, member map, badge map | `(table members badges)` with the resulting BadgeTable and maps | Proof, assertion, or fuel failure |

The member and badge maps and the false-prefix cache are alists in insertion
order. A failure is the entire result in place of any value and object pair.

## Proof operations used by certificates

| Function | Arguments in order | Result | Failure |
| --- | --- | --- | --- |
| `l1-primitive-warrant-constant` | Proof, term | Equality Step for a WarrantProof constant computation, or `nil` | Proof or term failure |
| `l1-primitive-proof-simplify` | Proof, term, evidence Step list, definition symbol list | Equality Step for simplification, or `nil`. Proof kind `:l1-warrant` uses the WarrantProof comparisons, selector computations, and tameness rule. | Proof, term, or fuel failure |
