# Records

A Records object has the form `(:t4-records library)`. Its library
has the form specified in `prover/sig/library.md`. Terms, signed tests
and Steps use the forms in `prover/sig/proof.md` and
`prover/sig/termination.md`.

The symbol constants are `*t4-records-record*`, `*t4-records-wrapped*`,
`*t4-records-before*`, `*t4-records-insert*`, `*t4-records-delete*`,
`*t4-records-assoc*`, `*t4-records-get*`, `*t4-records-set*`,
`*t4-records-atom*`, `*t4-records-endp*`, `*t4-records-null*`,
`*t4-records-w*`, `*t4-records-fields*`, `*t4-records-backing*`,
`*t4-records-pack*` and `*t4-records-update*`.

| Function | Arguments and result |
|---|---|
| `(t4-records-first-key record)` | Record term. Returns its first key term. |
| `(t4-records-above lower record)` | Lower key and record terms. Returns the condition that the record is atomic or its first key is above the lower key. |
| `(t4-records-field key record)` | Key and record terms. Returns the value lookup term. |
| `(t4-records-valid-backing backing)` | Backing term. Returns the condition that the backing is nil or is outside the record wrapper class. |
| `(t4-records-records-init lib)` | Library. Returns a Records object with that library. |
| `(t4-records-records-lib records)` | Records object. Returns its library. |
| `(t4-records-records-has records name)` | Records object and unprefixed fact name string. Tests for the corresponding fact. |

These calls do not return a failure. In the method calls below, the first
argument is a Records object. Each call may return a failure as its entire
result. A proof construction returns a Step unless specified otherwise.

| Method | Arguments after `records` and result |
|---|---|
| `t4-records-records-use` | Unprefixed name string, term list, premise Step list. Uses the fact with bindings for X, Y, Z and W in that order. |
| `t4-records-records-choose` | Equation Step and condition Step. Selects the branch on the right of the equation. |
| `t4-records-records-unfold-side` | Call term, shape Step, Boolean. Unfolds the call and takes the side determined by the shape Step. |
| `t4-records-records-cons` | Pair construction term. Proves that it is a cons. |
| `t4-records-records-projections` | Step, pair construction term. Rewrites the first literal with the CAR and CDR equations in order. |
| `t4-records-records-lift` | Step, equation Step, result template. Rewrites the result slots using the reversed equation. |
| `t4-records-records-nil-from-denial` | Denial Step. Proves equality to NIL. |
| `t4-records-records-denial-from-nil` | Equation Step with quoted NIL on the right. Proves the denial of its left side. |
| `t4-records-records-nonempty` | Cons shape Step. Proves the object is nonempty. |
| `t4-records-records-nonempty-record` | Record Step, nonempty Step. Proves the object is a cons. |
| `t4-records-records-null-test` | Step, Boolean. Converts a signed fact to the corresponding NULL test fact. |
| `t4-records-records-denied-null` | Denied NULL hypothesis Step. Proves the object is nonempty. |
| `t4-records-records-change-args` | Term, list of `(index equation-step)` pairs. Rewrites the arguments in list order. |
| `t4-records-records-transitive` | Two ordering Steps. Proves the strict composition. |
| `t4-records-records-reversed-distinct` | Inequality Step. Reverses the operands of the inequality. |
| `t4-records-records-reverse-order` | Denied strict ordering Step, inequality Step. Proves the opposite strict ordering. |
| `t4-records-records-record-atom` | Record Step, atomic shape Step. Proves the object is NIL. |
| `t4-records-records-weaken-order` | Strict bound Step, tail term. Proves the bound as a condition that allows an atomic tail. |
| `t4-records-records-empty-order` | Lower key term. Proves that it bounds an empty record. |
| `t4-records-records-record-nil` | No further arguments. Proves that NIL is a record. |
| `t4-records-records-assoc-cons` | Key term, pair construction term. Gives the lookup equation on the constructed record. |
| `t4-records-records-assoc-nil` | Key term. Gives the lookup equation on NIL. |
| `t4-records-records-before-distinct` | Strict ordering Step. Proves the keys differ. |
| `t4-records-records-wrapped-record` | Record Step. Proves the resulting wrapper test. |
| `t4-records-records-invalid-record` | Denied wrapper test Step. Proves the object is outside the record class. |
| `t4-records-records-invalid-nonempty` | Denied wrapper test Step. Proves the object is nonempty. |
| `t4-records-records-backing-proof` | Denied wrapper test Step. Proves the backing condition. |
| `t4-records-records-nil-backing` | No further arguments. Proves the backing condition for NIL. |
| `t4-records-records-wrapper-parts` | Denied record Step, wrapper Step. Returns the list of Steps for cons shape, invalid backing, valid fields and nonempty fields. |
| `t4-records-records-pack-view` | Equation Step, backing condition Step, optional fields condition Step. Pass `nil` for the omitted fields condition. Opens and selects the packed representation. |
| `t4-records-records-field-view` | Key term, equation Step. Lifts the equation into the record operand of a field lookup. |

The next methods return `(cons result records)` with the resulting
Records object. The `represent` method returns the resulting Records
object directly. A method retains existing auxiliary lemmas and adds
new ones in proof construction order.

| Method | Arguments after `records` and result |
|---|---|
| `t4-records-records-cons-record` | Head and tail terms. Gives the record test equation on their cons. |
| `t4-records-records-components` | Record Step, cons shape Step. Gives the list of Steps for head shape, head value, tail validity and tail order. |
| `t4-records-records-ordered-record` | Head cons Step, head value Step, tail record Step and lower bound Step. Proves validity of the constructed record. |
| `t4-records-records-insert-order` | Key, value, record and lower key terms, bound Steps for the key and record. Proves the insertion has the lower bound. |
| `t4-records-records-delete-order` | Key, record and lower key terms, record Step and old bound Step. Proves the deletion has the lower bound. |
| `t4-records-records-typed-insert` | Key, value and record terms, record Step and nonempty value Step. Proves validity after insertion. |
| `t4-records-records-typed-delete` | Key and record terms, record Step. Proves validity after deletion. |
| `t4-records-records-missing-below` | Key and record terms, record Step and lower bound Step. Proves that the lookup is absent. |
| `t4-records-records-updated-lookup` | Query, update key, update value and record terms, optional record Step. Pass `:none` for deletion and `nil` for an omitted record Step. Gives the lookup equation after insertion or deletion. |
| `t4-records-records-represent` | No further arguments. Adds the fields, backing, pack and update definitions when absent. |
| `t4-records-records-decoders` | Object term, signed record Step, optional signed wrapper Step. Pass `nil` for the omitted wrapper Step. Gives a list of the fields and backing equations, in that order. |
| `t4-records-records-decoded-types` | Object term. Gives the list of Steps for record validity of the fields and validity of the backing. |
| `t4-records-records-packed-types` | Record and backing terms, record Step and backing validity Step. Gives a list of the fields and backing projection equations in that order. |
| `t4-records-records-reconstruct` | Object term. Equates packing the decoded fields and backing to the object. |
| `t4-records-records-get-view` | Key and object terms. Gives the public lookup equation in terms of the decoded fields. |
| `t4-records-records-typed-update` | Key, value and raw record terms, record Step. Proves validity after update. |
| `t4-records-records-update-view` | Query, update key, value and raw record terms, record Step. Gives the raw lookup equation after update. |
| `t4-records-records-set-view` | Key, value and object terms. Gives the public write equation in terms of update and pack. |
| `t4-records-records-get-after-set` | Query, update key, value and object terms. Gives the public lookup equation after a public write. |

`(t4-records-record-preservation lib formula)` and
`(t4-records-record-read lib formula)` take a Library and a formula
term. They return `(cons step-or-nil library)` with the resulting
Library, or a failure. The first proves record validity after a public
write and the second proves a public read after a public write.

## Simplification and arithmetic replies

`unfold-side`, `nonempty-record`, `null-test`, `denied-null`,
`record-atom`, and `assoc-cons` return `(cons step records)`.
These return shapes apply whenever the proof construction uses a
simplification that can install an auxiliary lemma.

`(t4-records-record-preservation-with-replies lib formula replies)` and
`(t4-records-record-read-with-replies lib formula replies)` accept the
request protocol in `prover/t4/sig/constructors.md`. Each recognized formula
requests `:use-arithmetic` with no operation arguments before constructing
the proof. Pass an empty reply list for the initial call. An unrecognized
formula returns `(cons nil lib)` directly.

`(t4-records-prove records term evidence definitions)` takes a Records
object, a term, a list of evidence Steps and an ordered list of definition
symbols. It returns `(cons step records)` with the resulting Records
object, or a failure from proof construction.
