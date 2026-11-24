# Floor reassociation

The floor reassociation proof gets the second factor of the numerator
from the second argument of the product inside the operation term. The
consequent proof uses that factor in its associativity and commutation
Steps.

`grep -nE 'b2-products-floor-reassociate-consequent|caddr \(cadr operation\)' prover/b2/products.lisp` shows the proof operations. The command was run on 2026-11-23.
