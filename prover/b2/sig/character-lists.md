# Character-list preservation

`lib` is a Library as specified in `prover/sig/library.md`. A term, a symbol, and a Step have the forms in `prover/sig/proof.md`. Evidence is a list of Steps in the supplied order. A pair `(cons step lib)` contains the Step and the Library with any facts and entries added by the call. Entries are in append order and facts are in insertion order. A failure is the entire result.

| ACL2 call | Result | Failure |
|---|---|---|
| `(b2-character-lists-pack-characters lib name formula)` | Pair of the Step for the character-list packing formula and the resulting Library. `name` is the theorem symbol or `nil`. | Failure from reading the formula or constructing the proof. |
| `(b2-character-lists-proper-characters lib typed)` | Pair of the corresponding true-list Step and the resulting Library. `typed` is a character-list Step. | Failure from proof construction. |
| `(b2-character-lists-typed-cell lib character typed-tail facts)` | Step for character-list type of the cons with term `character` and the tail of the character-list Step `typed-tail`. Pass `nil` for omitted evidence `facts`. | Failure from proof construction. |
| `(b2-character-lists-digit-type lib digit)` | Pair of the Step for the character type of the conversion of term `digit` and the resulting Library. | Failure from proof construction. |
| `(b2-character-lists-decimal-type lib number accumulator)` | Pair of the Step for the character-list type of decimal rendering and the resulting Library. `number` and `accumulator` are terms. | Failure from proof construction. |
| `(b2-character-lists-atom-type lib value kind)` | Pair of the Step for the character-list type of decimal atom rendering and the resulting Library. `value` is a term and `kind` is the numeric predicate symbol or `nil` for the default. | Failure from proof construction. |

`*b2-character-lists-character-list*`, `*b2-character-lists-pack-list*`, and `*b2-character-lists-pack-tree*` are prover symbols. `*b2-character-lists-pack-theorems*` is the list of the two packing theorem symbols, in order of their serialized text.

The other constants are `*b2-character-lists-append*`, `*b2-character-lists-digit*`, `*b2-character-lists-num-chars*`, `*b2-character-lists-atom-chars*`, `*b2-character-lists-print-base*`, `*b2-character-lists-member*`, `*b2-character-lists-append-type*`, `*b2-character-lists-coerce*`, `*b2-character-lists-ten*`, `*b2-character-lists-ans*`, and `*b2-character-lists-list*`.

`(b2-character-lists-character-result lib value evidence other)` returns a pair with the character-list Step for result term `value`. `(b2-character-lists-analyze-result lib call evidence other)` returns a pair with the character-list Step for every result branch of application term `call`. Both can return a failure from proof construction. `other` represents the proof callback. The atom-rendering callback is `(:atom kind)`, and the packing callback is `(:pack)`. A callback supplied as `(:replies . replies)` uses an association list of `(value evidence)` keys to callback results. A callback result is a Step and Library pair, or a failure.
