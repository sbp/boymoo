# Lexicographic comparison

Terms, Proof and Steps use the forms in `prover/sig/proof.md`.
`*l1-lexicographic-numeric-equal*`, `*l1-lexicographic-fix*` and
`*l1-lexicographic-control*` denote the numeric equality function, the
numeric fix function and the two names unfolded by the control proof.

| Call | Arguments and result | Failure |
|---|---|---|
| `(l1-lexicographic-number-length proof argument)` | Prove that the length of the argument term is an ACL2 number. | Proof construction. |
| `(l1-lexicographic-cancel-successor proof argument)` | Return the Step cancelling addition of one to the length of the argument term. | Proof construction. |
| `(l1-lexicographic-equal-tail-lengths proof x y same-length)` | From the equal length test term for `x` and `y`, prove their tails have equal length. | Proof construction. |
| `(l1-lexicographic-not-less-when-equal proof equality)` | Return the Step refuting a strict comparison of the two terms of the equality Step. | Malformed equality or proof construction. |
| `(l1-lexicographic-replace-value term original replacement)` | Replace the original term in value positions, with quoted contents left intact. | Malformed term. |
| `(l1-lexicographic-compare-branches proof left right changed)` | Prove the equality of conditional terms `left` and `right` using equality Step `changed` at the changed branch. | Failed assertion, malformed conditional or proof construction. |
| `(l1-lexicographic-length-wrapper proof function formals body)` | Return the comparison recurrence Step for function symbol `function`, its formal symbols and the translated body. | `unsupported-application`, failed assertion, malformed term or proof construction. |
