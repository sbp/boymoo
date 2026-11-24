# Reversal involution

`(b2-reversal-reversal library formula)` takes the B2 Library and the
reversal-involution theorem term, including its hypotheses. It returns
`(cons step library)` with the proof Step and the Library extended by the
append-singleton lemma. Failure from reading the formula or constructing the
proof is the entire result.

`*b2-reversal-item*` is the symbol datum for `ACL2::ITEM`.
