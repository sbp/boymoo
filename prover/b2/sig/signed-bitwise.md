# Signed bitwise proofs

Libraries, terms and Steps use the forms specified in `prover/sig/library.md`
and `prover/sig/proof.md`. `*b2-signed-bitwise-bitp*` and
`*b2-signed-bitwise-logand*` are the prover symbols `BITP` and `LOGAND`.

| Call | Arguments and result |
|---|---|
| `(b2-signed-bitwise-bit-from-bounds lib typed lower upper)` | `typed` proves its argument integer, `lower` proves it nonnegative, and `upper` proves it strictly below two. Returns a Step proving it is a bit. |
| `(b2-signed-bitwise-excluded-half lib half value equation excluded)` | `half` and `value` are terms. `equation` proves the unchanged expansion of the dividend and `excluded` excludes the corresponding fixed point of the dividend. Returns a Step excluding equality of `half` and `value`. |
| `(b2-signed-bitwise-half-decrease lib term typed nonzero nonminusone floor-type)` | `typed`, `nonzero` and `nonminusone` are Steps proving the corresponding properties of `term`. Returns `(cons step lib)` proving that halving the integer decreases its count. |
| `(b2-signed-bitwise-integer-logand lib a b floor-type)` | `a` and `b` are terms. Returns `(cons step lib)` proving their bitwise conjunction integer. |

Each function may return a failure as the entire result. A returned Library
includes any lemmas added by the call. The floor-type callback takes a Library
and two terms and returns `(cons step updated-lib)` or a failure. Pass its reply
as `floor-type`, or `nil` to request the arguments if the callback is needed.
In place of a proof result, the function then returns `(cons request lib)`,
where `request` is `(:call :b2-signed-bitwise-floor-type lib i j)`. Call the
callback on that Library and those terms, then repeat the original call on its
original Library with the reply supplied. The callback is called at most once
and only with the terms `X` and quoted `2`.

| Call | Arguments and result |
|---|---|
| `(b2-signed-bitwise-floor-request-p result)` | Recognizes the result pair of a pending floor-type callback. |
| `(b2-signed-bitwise-step-at step index)` | Returns the element at the zero-based index of the Step's first literal, or a failure. |
| `(b2-signed-bitwise-assumptions lib tests)` | Returns the assumption Steps for the ordered list of `(test holds)` pairs, or a failure. |
| `(b2-signed-bitwise-known-step known term)` | The Step for `term` in the evidence table, or a failure if it is absent. |
| `(b2-signed-bitwise-by-value-join lib value template yes no)` | Joins the two proofs of the template for conditional term `value` in true then false branch order. May return a failure. |
| `(b2-signed-bitwise-by-value-check value template step)` | Returns the Step when its first literal is the template instantiated with `value`, or a failure. |
