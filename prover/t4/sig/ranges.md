# Arithmetic range descent

`lib` is a Library as in `prover/sig/library.md`. Terms and Steps have the
forms in `prover/sig/proof.md`. `goal` is a strict ordinal comparison of
two gap measures. `formals` are the definition's formal symbols in
order. The first three formals are the lower endpoint, upper endpoint
and stride.

`(t4-ranges-range-descent lib goal evidence formals)` returns the
descent Step, a failure, or `(:call :require term)` for the next required
hypothesis. The `evidence` argument is the list of replies to the
Evidence requirements of this invocation, in order. On a request,
call `t4-structural-evidence-require` on the Evidence and `term`, keep the
resulting Evidence, and append the Step or failure to the replies. Start
with `nil` and repeat the call with the extended list. Use
`t4-ranges-request-p` to recognize a request.

`(t4-ranges-range-descent-queries goal formals)` gives the five
requested terms in order, or a failure while reading `goal` or
`formals`. A caller may use this order to obtain all the replies
in one pass, stopping at the first failure.
