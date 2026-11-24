# Abstract list constraints

`lib` is a Library as specified in `prover/sig/library.md`. Terms and Steps
have the forms in `prover/sig/proof.md`. `index` is the B1 search FactIndex.
Pass `nil` for an absent index. The index is fixed
throughout a recipe. `formula` is the translated theorem term. Every
recipe may return a failure in place of its result. A result paired with
a Library is `(cons value lib)`, with any new entries and facts in
insertion order.

`(b1-abstract-lists-list-signature lib predicate index)` takes the symbol
at the head of a predicate. It returns `(position cons-law atom-law)`,
or `nil` if the index supplies no signature. `position` is the one-based
argument index of the recursive list and each law is a fact name. The
cons claims are visited in reverse insertion order. The atom claim is
selected by `b1-logic-matching-claim`. The search can return a failure on
malformed claims.

A `ListType` is `(:b1-list-type lib predicate tag position cons-law atom-law index)`.
`predicate` is the whole predicate application, `tag` is the last two
characters of its name, and the three signature fields have the meanings
above. The constructor falls back to the named `LIST-TYPE` definition and
`ELEM-TYPE` constraints when the index supplies no signature.

| Call | Result |
|---|---|
| `(b1-abstract-lists-list-type-init lib predicate index)` | ListType for the predicate application. |
| `(b1-abstract-lists-list-type-lib typed)` | Library of `typed`. |
| `(b1-abstract-lists-list-type-predicate typed)` | Predicate application of `typed`. |
| `(b1-abstract-lists-list-type-tag typed)` | Tag string of `typed`. |
| `(b1-abstract-lists-list-type-position typed)` | Recursive argument position of `typed`. |
| `(b1-abstract-lists-list-type-cons-law typed)` | Cons constraint name of `typed`. |
| `(b1-abstract-lists-list-type-atom-law typed)` | Atom constraint name of `typed`. |
| `(b1-abstract-lists-list-type-index typed)` | FactIndex of `typed`, or `nil`. |
| `(b1-abstract-lists-list-type-with-lib typed lib)` | ListType with the given Library and the same remaining fields. |
| `(b1-abstract-lists-list-type-prior typed operation goal)` | Step for `goal` from an earlier list law. `operation` is its operation name string. |
| `(b1-abstract-lists-list-type-on typed items)` | Predicate application with term `items` in the recursive argument. |
| `(b1-abstract-lists-list-type-constructor typed term)` | Cons constraint Step instantiated to predicate application `term`. |
| `(b1-abstract-lists-list-type-at-atom typed term atom)` | Atom constraint Step at application `term`, using the non-cons Step `atom`. |
| `(b1-abstract-lists-list-type-empty typed)` | Step proving the predicate on quoted NIL. |
| `(b1-abstract-lists-list-type-reconstructed typed source cons)` | Step from typing Step `source` with its list argument reconstructed using the nonempty Step `cons`. |
| `(b1-abstract-lists-list-type-fields typed source cons)` | List of the element typing Step and tail typing Step from recognizer Step `source` and nonempty Step `cons`. |
| `(b1-abstract-lists-list-type-pair typed cons element tail)` | Step typing the cons term `cons` from typing Steps for its `element` and `tail`. |
| `(b1-abstract-lists-list-type-proper typed source)` | Step proving properness of the list in typing Step `source`. |

| Call | Result |
|---|---|
| `(b1-abstract-lists-abstract-list-proper lib formula index)` | Step that a typed list is proper. |
| `(b1-abstract-lists-abstract-list-cons lib formula index)` | Step that cons preserves list type. |
| `(b1-abstract-lists-abstract-list-cdr lib formula index)` | Step that cdr preserves list type. |
| `(b1-abstract-lists-abstract-list-car lib formula index)` | Step that car of a typed nonempty list has the element type. |
| `(b1-abstract-lists-abstract-list-member lib formula index)` | Step that a member of a typed list has the element type. |
| `(b1-abstract-lists-abstract-list-memberp lib formula index)` | Pair of the corresponding `MEMBERP-EQUAL` Step and the resulting Library. |
| `(b1-abstract-lists-abstract-list-append lib formula index)` | Step for the type of append. |
| `(b1-abstract-lists-reuse-abstract-list lib formula index)` | Step for a cdr-based list operation. |
| `(b1-abstract-lists-abstract-list-nthcdr lib formula index)` | Step for the type of `NTHCDR`. |
| `(b1-abstract-lists-abstract-make-list lib formula index)` | Step for the type of `MAKE-LIST-AC`. |
| `(b1-abstract-lists-abstract-list-reverse lib formula index)` | Step for the type of `REVERSE`. |
| `(b1-abstract-lists-abstract-list-initial-sublist lib formula index)` | Step that an initial sublist retains the list type. |
| `(b1-abstract-lists-abstract-list-bounded-operation lib formula index)` | Pair of the type Step for bounded take or update and the resulting Library. |
| `(b1-abstract-lists-abstract-list-nth lib formula index)` | Pair of the bounded `NTH` element typing Step and the resulting Library. |
| `(b1-abstract-lists-abstract-list-put-nth lib formula index)` | Pair of the `PUT-NTH` typing Step and the resulting Library. |
| `(b1-abstract-lists-abstract-list-butlast lib formula index)` | Step for the type of `BUTLAST`. |
| `(b1-abstract-lists-abstract-list-subseq lib formula index)` | Pair of the bounded `SUBSEQ` typing Step and the resulting Library. |

| Call | Result |
|---|---|
| `(b1-abstract-lists-positive-index lib index)` | List of the integrality and positivity Steps for term `index`, under `(not (ZP index))`. |
| `(b1-abstract-lists-index-descent lib index next-index)` | Step proving the ordinal decrease after decrementing the positive term `index` to term `next-index`. |
| `(b1-abstract-lists-decreased-formula lib formula index next-index mapping)` | Induction hypothesis Step, substituting term bindings from the insertion-ordered alist `mapping` with entries `(variable . term)`. |
| `(b1-abstract-lists-nfix-at-zero-test lib index zp)` | Step equating ACL2's `NFIX` of term `index` to zero under Step `zp`. |
| `(b1-abstract-lists-shift-fixed-index lib index next-index)` | Pair of the list of index integrality, index `NFIX` identity, and next index `NFIX` identity Steps, and the resulting Library. |
| `(b1-abstract-lists-shifted-positive-index lib next-index integer-index positive-bound)` | Pair of the list of integrality and nonnegativity Steps for term `next-index`, and the resulting Library. The last two arguments are integrality and strict positivity Steps for the original index. |
| `(b1-abstract-lists-smaller-strict-index-bound lib limit cons index next-index)` | Pair of the equality Step aligning comparison term `limit` with the smaller bound under nonempty Step `cons`, and the resulting Library. |
| `(b1-abstract-lists-beyond-empty-list lib comparison atom)` | Step refuting comparison term `comparison` under non-cons Step `atom`. |
| `(b1-abstract-lists-length-after-dropping lib index items evidence)` | Pair of the Step for the length of `NTHCDR` and the resulting Library. `index` and `items` are terms, and `evidence` lists the bound and integrality Steps in premise order. |

The term constants are `*b1-abstract-lists-last*`,
`*b1-abstract-lists-reverse*`, `*b1-abstract-lists-revappend*`,
`*b1-abstract-lists-null*`, `*b1-abstract-lists-nthcdr*`,
`*b1-abstract-lists-cons-hint*`, and `*b1-abstract-lists-acl2-nfix*`.

`(b1-abstract-lists-abstract-list-butlast-with-library lib formula index)`
returns `(cons step lib)` for `BUTLAST`, including the auxiliary number
lemmas that the calculation can add. It can return a failure. Use this
entry point in theorem dispatch. The step-only entry point returns the
Step component.

For `b1-abstract-lists-list-signature`, use `:none` for an absent predicate head.
