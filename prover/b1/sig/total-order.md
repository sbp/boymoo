# Total order

`lib` is a B1 Library. Terms, symbols, and Steps have the forms in
`prover/sig/proof.md`. Each function can return a failure from the proof
operations it uses. The Library is unchanged by these functions.

`*b1-total-order-strict*` and `*b1-total-order-order*` are the prover symbols
for `ACL2::<<` and `ACL2::LEXORDER`.

| ACL2 call | Result |
|---|---|
| `(b1-total-order-strict-definition lib comparison)` | An equality Step opening the strict comparison term `comparison`. |
| `(b1-total-order-strict-components lib strict)` | The list of Steps for the conjuncts of the strict comparison Step `strict`, in order. |
| `(b1-total-order-assemble-strict lib conclusion ordered unequal)` | A Step for the strict comparison term `conclusion` using the weak comparison Step `ordered` and inequality Step `unequal`. |
| `(b1-total-order-order-fact lib name args)` | An instantiated axiom Step for `LEXORDER-` followed by the string `name`, with the list of argument terms `args` in order. |
| `(b1-total-order-antisymmetric lib first second)` | The equality Step implied by the opposing weak comparison Steps `first` and `second`. |
| `(b1-total-order-strict-irreflexive lib formula)` | A Step for the strict-order irreflexivity formula. |
| `(b1-total-order-strict-implies-order lib formula)` | A Step for the implication from strict to weak order in `formula`. |
| `(b1-total-order-strict-asymmetric lib formula)` | A Step for the strict-order asymmetry formula. |
| `(b1-total-order-strict-transitive lib formula)` | A Step for the strict-order transitivity formula. |
| `(b1-total-order-strict-total lib formula)` | A Step for the strict-order trichotomy formula. |
