# Association lookup

The constants `*b1-records-assoc*` and `*b1-records-v*` are the symbols
`ACL2::ASSOC-EQUAL` and `ACL2::V` in prover term form.

`(b1-records-association-step lib term)` takes a Library and a prover
term. It returns `(cons step lib)`. The result Step is the lookup
equation for a quoted key and an association list constructed by CONS
from a pair with a quoted key. Other terms give `nil` in the Step
position. The resulting Library includes any lookup lemma installed
by the call. A failure is the entire result.
