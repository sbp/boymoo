# Input fields

The `lib` argument is a Library as specified in `prover/sig/library.md`. Terms and Steps have the forms in `prover/sig/proof.md`. An `index` argument is an integer. An equality Step has an equality as its first literal.

The symbol constants `*t2-input-fields-mv-nth*`, `*t2-input-fields-zp*`, `*t2-input-fields-update*`, `*t2-input-fields-channels*`, `*t2-input-fields-put-global*`, `*t2-input-fields-update-global*`, `*t2-input-fields-oracle-state*`, `*t2-input-fields-read-oracle*`, `*t2-input-fields-print-updates*`, `*t2-input-fields-read-object*`, `*t2-input-fields-nth*`, `*t2-input-fields-endp*`, `*t2-input-fields-atom*`, `*t2-input-fields-assoc*`, `*t2-input-fields-open-channel*`, `*t2-input-fields-open-any*`, `*t2-input-fields-type*` and `*t2-input-fields-add-pair*` denote the corresponding prover symbol data.

| ACL2 call | Arguments and result | Failure |
|---|---|---|
| `(t2-input-fields-select lib equality evidence)` | Equality Step and evidence Step for a branch of its right side. Returns the equality Step reduced to that branch. | A failure from proof construction. |
| `(t2-input-fields-negated-value lib equation)` | Equality Step with quoted `NIL` on the right. Returns the Step proving the negation of its left side. | A failure for a different right side or failed proof construction. |
| `(t2-input-fields-constant-zp lib index)` | Quoted index value as an integer. Returns the Step establishing whether its `ZP` test holds. | A failure for a negative index or failed proof construction. |
| `(t2-input-fields-end-condition lib term)` | An end-test term. Returns its unfolded equality Step, opening the resulting call as well when the input calls `ENDP`. | A failure from proof construction. |
| `(t2-input-fields-cons-projection lib selector index result)` | Selector symbol, index, and a `CONS` term. Returns the equality Step for selection from the visible cons spine. | A failure when the required cons spine is absent or proof construction fails. |
| `(t2-input-fields-bindings lib term)` | Term. Returns the equality Step reducing lambda applications and calls of `RETURN-LAST`, or `nil` if none are reduced. | A failure from proof construction or `Fuel` on exhaustion. |
| `(t2-input-fields-result-state channel state)` | Channel and state terms. Returns the term for the state component of `(READ-OBJECT channel state)`. | None. |
| `(t2-input-fields-project-cons-fields lib term)` | Term. Returns the equality Step simplifying `CAR` and `CDR` of visible cons cells, or `nil` if none are simplified. | A failure from reading a term or constructing a proof. |
| `(t2-input-fields-assoc-write lib query key value table)` | Query, key, value and table terms. Returns the equality Step for looking up the query after writing the key and value into the table. | A failure from proof construction. |
| `(t2-input-fields-lookup lib query channel state reads-value)` | Query, channel and state terms, and the branch Boolean. Returns `(step test)` with the lookup equality Step and the test for a successful read. | A failure from proof construction. |
| `(t2-input-fields-type-check lib term)` | Type test term. Returns an equality Step opening the test and reducing its bindings. | A failure from proof construction. |
| `(t2-input-fields-replace-lookup lib equation replacement)` | Equality Step and replacement equality Step. Returns the Step rewriting the lookup in the right side of `equation`. | A failure from proof construction. |
| `(t2-input-fields-build lib)` | Returns the Library extended with the input field lemmas in proof construction order. | A failure from proof construction. |

| ACL2 call | Arguments and result | Failure |
|---|---|---|
| `(t2-input-fields-input-slot lib)` | Returns the Library with the input slot and slot write lemmas. | A failure from proof construction. |
| `(t2-input-fields-other-updates lib)` | Returns the Library with input slot preservation for oracle and global writes, oracle reads, and print updates. | A failure from proof construction. |
| `(t2-input-fields-other-updates-leaf n value tests lib projected)` | Fuel, result term, signed tests, Library and the term projecting state from the oracle read. Returns a Step equating the input channels of the result and the original state. | `Fuel` on exhaustion, or a failure for an unexpected result term or failed proof construction. |
| `(t2-input-fields-project-read lib)` | Returns the Library with the read result flag and input slot lemmas. | A failure from proof construction. |
| `(t2-input-fields-preserve-channel-type lib)` | Returns the Library with preservation of the channel's input type. | A failure from proof construction. |
| `(t2-input-fields-any-type-holds lib tests evidence)` | Type test term and evidence Step. Returns the Step proving the test term from evidence for one of its alternatives. | A failure from proof construction or an unmet precondition on the test structure. |
| `(t2-input-fields-preserve-any-channel-by-type n step lib written)` | Fuel, Step for the original state, Library and unfolded type-test equality Step for the updated state. Returns the Step proving the updated type test. | `Fuel` or a failure from proof construction. |
| `(t2-input-fields-preserve-any-channel lib)` | Returns the Library with preservation of the channel's input type without specifying the type. | A failure from proof construction. |
| `(t2-input-fields-shorter-contents lib)` | Returns the Library with the length decrease for a successful read. | A failure from proof construction. |

Use `1000000` as the initial fuel for the lifted functions.
