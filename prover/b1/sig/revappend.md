# Reversal with an accumulator

`lib` is a Library as in `prover/sig/library.md`. Terms and Steps have
the form specified in `prover/sig/proof.md`. All the functions below can
return a failure except `b1-revappend-extend-accumulator`. A failure is the
entire result.

The term symbol constants have the prefix `*b1-revappend-` and the suffix
`*`. Their names are `rev` for `COMMON-LISP::REVAPPEND`, `last` for
`COMMON-LISP::LAST`, `butlast` for `COMMON-LISP::BUTLAST`, `append`
for `ACL2::BINARY-APPEND`, `fix` for `ACL2::TRUE-LIST-FIX`, `iff`
for `ACL2::IFF`, `member` for `ACL2::MEMBER-EQUAL`, `intersection`
for `ACL2::INTERSECTION-EQUAL`, `take` for `ACL2::TAKE`, `nfix`
for `ACL2::NFIX`, `acc` for `ACL2::ACC`, and `item` for
`ACL2::A`.

| Call | Result |
|---|---|
| `(b1-revappend-open-list lib term evidence)` | Equality Step opening the head of the term with the evidence Steps in order. Pass `nil` for no evidence. |
| `(b1-revappend-extend-accumulator x accumulator)` | Term for adjoining the car of term `x` to term `accumulator`. |
| `(b1-revappend-list-induction-prepare lib formula x accumulator)` | The list `(induction test cons hypothesis)`, where `test` is the cons test on term `x`, `cons` is its assumption Step, and `hypothesis` is the induction hypothesis Step. Pass `nil` for an omitted accumulator. |
| `(b1-revappend-list-induction lib preparation base step)` | Induction Step for the formula in `preparation`, using the Steps `base` and `step` for the atom and cons cases. |
| `(b1-revappend-lift-argument lib expression argument index)` | Equality Step lifting an equality Step `argument` to the one-based argument position `index` of term `expression`. |
| `(b1-revappend-accumulator-commutation lib formula)` | Step moving an operation on the accumulator through reversal. |
| `(b1-revappend-revappend-with-nil-accumulator lib formula)` | Step relating reversal and append with a nil accumulator. |
| `(b1-revappend-car-of-revappend lib formula)` | Step for the car of a reversal. |
| `(b1-revappend-consp-value lib consp)` | Equality Step to quoted T for the CONSP in Step `consp`. |
| `(b1-revappend-consp-of-revappend lib formula)` | Step for CONSP of a reversal. |
| `(b1-revappend-cons-is-nonempty lib consp)` | Step that the argument of the CONSP in Step `consp` is non-nil. |
| `(b1-revappend-revappend-nonempty lib formula)` | Step for the nonemptiness of a reversal. |
| `(b1-revappend-length-of-revappend lib formula)` | Step for the length of a reversal. |
| `(b1-revappend-revappend-of-list-fix lib formula)` | Step for reversal of a fixed list. |
| `(b1-revappend-reversed-twice lib formula)` | Step for reversal of a reversal. |
| `(b1-revappend-count-of-revappend lib formula)` | `(cons step lib)` for the count bound of a reversal, with any auxiliary lemmas. |
| `(b1-revappend-positive-length lib cons)` | Step for the positive length of the list in CONSP Step `cons`. |
| `(b1-revappend-reverse-not-unchanged lib formula)` | Step for changing the accumulator by reversing a nonempty list onto it. |
| `(b1-revappend-cons-value lib term)` | CONSP Step for a CONS term. |
| `(b1-revappend-right-disjunct lib term proof)` | Step for the conditional term `term`, given the Step `proof` for its second disjunct. |
| `(b1-revappend-nonempty-fold-of-reversal lib formula slot head-test)` | Step moving a reversal at one-based argument position `slot` through a fold with the term `head-test` for success at the head. |
| `(b1-revappend-member-of-revappend lib formula)` | `(cons step lib)` for membership of a reversal, with any auxiliary lemma. |
| `(b1-revappend-intersects-reversed-first lib formula)` | Step for intersection with a reversed first argument. |
| `(b1-revappend-intersects-reversed-second lib formula)` | `(cons step lib)` for intersection with a reversed second argument, with any auxiliary lemmas. |
| `(b1-revappend-unequal-lengths lib left right strict)` | Step that terms `left` and `right` differ, given a Step `strict` for their strictly ordered lengths. |
| `(b1-revappend-cons-equality lib left right)` | Step relating equality of two CONS terms to equality of their fields. |
| `(b1-revappend-revappend-pair-equality lib formula)` | Step for cancellation of equal-length accumulators in a reversal equality. |
| `(b1-revappend-butlast-once lib x cons tail-case)` | Equality Step for removing the last element of term `x`, given Steps for CONSP of `x` and the chosen case of CONSP of its cdr. |
| `(b1-revappend-cdr-of-revappend lib formula)` | Step for the cdr of a reversal. |

A list induction first prepares the hypothesis and the cons assumption.
The caller proves the cons case, assumes the test false, then proves the
atom case. The Library passed to the final call includes any additions
made while proving the cases. The accumulator substitution follows the
substitution for `x`, retaining that key's position if the terms are equal.
