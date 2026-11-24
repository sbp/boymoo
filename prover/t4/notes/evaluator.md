# Evaluator witnesses

Call `t4-evaluator-evaluator-witness` with `nil` as its first argument
to start. When the tactic requests a definition proof, supply
the result of `t4-slice-generate`, using the generated value on success.
For a used-prelude request, supply the value of `t4-slice-used-prelude`.
The protocol accepts both replies together as
`(:replies generation-reply prelude-reply)`.

The witness search visits candidates in the order described in
`prover/t4/sig/evaluator.md` and returns the first proof it finds.
