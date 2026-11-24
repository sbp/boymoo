# Bitwise conjunction

`lib` is a Library as in `prover/sig/library.md`. Terms and Steps use the
forms in `prover/sig/proof.md`. Each call with a Library can return a failure
in place of the listed result. A pair `(value . lib)` carries the
Library with any lemmas added during the call.

| ACL2 call | Arguments and result |
|---|---|
| `(b1-conjunction-halved term)` | Returns the term for the floor of `term` divided by two. |
| `(b1-conjunction-conjunction a b)` | Returns the term for the bitwise conjunction of `a` and `b`. |
| `(b1-conjunction-bit-conjunction a b yes no)` | Returns the term selecting `yes` when either operand is even and `no` otherwise. |
| `(b1-conjunction-reduction-at lib term equality)` | Returns the reflexive equality of `term` with every occurrence of the left side of `equality` on the result side rewritten. |
| `(b1-conjunction-signed-constant lib value)` | `value` quotes zero or minus one. Returns `((floor even) . lib)` with the floor and evenness Steps, in that order. |
| `(b1-conjunction-zip-from-integer lib integral zero)` | `integral` proves `(INTEGERP term)` and `zero` proves either equality of `term` to zero or its negation. Returns the corresponding Step for `(ZIP term)` or its negation. |
| `(b1-conjunction-logand-unit lib unit other integral first)` | `unit` quotes zero or minus one, `other` is the other operand, and `integral` proves its integrality. `first` is true when `unit` is the first operand. `integral` may be `nil` when `unit` is zero. Returns the Step reducing the conjunction. |
| `(b1-conjunction-joined-conjunction lib first second)` | The two Steps give the operands' integrality. Returns `(step . lib)` for the bit decomposition of their conjunction. |
| `(b1-conjunction-induction-half lib formula variables descent)` | `variables` is the ordered list of variables to replace by their halves, and `descent` is the comparison Step. Returns the induction hypothesis Step. |
| `(b1-conjunction-use-projection lib first second)` | The two Steps give the operands' integrality. Returns `((integral floor even) . lib)` with the three projection Steps for their conjunction. |
| `(b1-conjunction-projection-lemma lib)` | Returns `(name . lib)` with the symbol of the conjunction projection lemma. |
| `(b1-conjunction-zip-noninteger lib noninteger)` | `noninteger` proves that its term is nonintegral. Returns a Step that `ZIP` holds of that term. |
| `(b1-conjunction-zero-on-zip lib term zipped)` | `term` is a bitwise conjunction and `zipped` proves that `ZIP` holds of an operand. Returns the Step equating `term` to zero. |
| `(b1-conjunction-full-conjunction lib formula)` | `formula` states that the conjunction is minus one exactly when both operands are minus one. Returns `(step . lib)` proving the formula. |
| `(b1-conjunction-associated-conjunction lib formula)` | `formula` states associativity of bitwise conjunction. Returns `(step . lib)` proving the formula. |
