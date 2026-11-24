# Sign proofs

`lib` is a Library. `numeric`, `rational`, `ra`, `rb`, `proof`, `absent`, `scalar-type`, `first`, `second` and `neg-complex` are Steps where supplied. `numeric` proves a number recognizer and the rational evidence proves a rational recognizer. Terms, Steps and Library objects follow `prover/sig/proof.md` and `prover/sig/library.md`. A sign or orientation is an integer. A Boolean is `t` or `nil`. A missing optional Step is `nil`.

A `Signs` value is the list `(sign negative zero positive)`, where the last three fields are Steps for the signed comparisons or their denials. `(h3-book-signs-make-signs sign negative zero positive)` constructs it. `(h3-book-signs-signs-sign signs)`, `(h3-book-signs-signs-negative signs)`, `(h3-book-signs-signs-zero signs)` and `(h3-book-signs-signs-positive signs)` read the fields. `(h3-book-signs-signs-at signs sign)` reads the field at zero-based index `sign + 1`. A negative index counts from the end. An invalid or out-of-range index gives a failure.

The constants are `*h3-book-signs-booleanp*`, `*h3-book-signs-case-split*`, `*h3-book-signs-complexp*`, `*h3-book-signs-prefix*`, `*h3-book-signs-sign-names*` and `*h3-book-signs-product-signs*`. The sign names are an alist in insertion order `-1`, `0`, `1`. The product names form a list ordered by their string representations.

Every proof operation can return a failure as its entire result, except `sign-test` on integer signs. A result written `(cons value lib)` pairs the value with the Library after any auxiliary lemmas have been added. An inapplicable recipe returns `nil` in the value position.

| Call | Result |
|---|---|
| `(h3-book-signs-sign-test term sign)` | The order or equality term testing the sign. |
| `(h3-book-signs-number lib rational)` | Step proving the rational argument is numeric. |
| `(h3-book-signs-positive-reflection lib term)` | Step expressing positivity as negativity of the opposite. |
| `(h3-book-signs-negative-reflection lib numeric)` | `(cons step lib)` for negativity expressed as positivity of the opposite. |
| `(h3-book-signs-zero-contradiction lib term index sign)` | Step disproving equality to zero using the strict comparison Step `sign` and the given rewrite index. |
| `(h3-book-signs-sign-evidence lib numeric sign proof)` | `(cons signs lib)` for the three literals derived from one signed Step. |
| `(h3-book-signs-predicate-value lib proof)` | `(cons step lib)` equating the predicate with its Boolean value. |
| `(h3-book-signs-minus-product lib a b lefthand)` | `(cons step lib)` for a negated factor moved outside the product. The default `lefthand` is `nil`. |
| `(h3-book-signs-times-negative-one lib numeric)` | `(cons step lib)` equating multiplication by negative one to unary negation. |
| `(h3-book-signs-rational-product lib ra rb)` | Step proving the product of the two rational arguments rational. |
| `(h3-book-signs-rational-sign lib ra rb sa sb)` | `(cons signs lib)` for the product of the rational arguments with Signs `sa` and `sb`. |
| `(h3-book-signs-rational-scaling lib ra rb sb orientation)` | `(cons step lib)` for the test of a rational product under the multiplier's Signs `sb`. |
| `(h3-book-signs-comparison-by-parts lib term orientation)` | `(cons step lib)` equating the sign test to comparison of real and imaginary parts. |
| `(h3-book-signs-scaled-parts lib term scalar-type)` | List of two Steps for the real and imaginary parts of the scaled term, with the real part first. |
| `(h3-book-signs-scaled-comparison lib term scalar-type scale orientation)` | `(cons step lib)` for the sign test of the product, using the scalar's Signs `scale`. |
| `(h3-book-signs-nonnumeric-signs lib term absent)` | List of Steps for the two default order comparisons followed by denial of equality to zero. |
| `(h3-book-signs-sign-conditions lib signs)` | `(cons steps lib)` where `steps` holds three sign literals followed by the three Boolean equalities, each in negative, zero, positive order. |
| `(h3-book-signs-scale-sign-goal lib formula term scalar swapped rational neg-complex)` | `(cons step lib)` proving the comparison formula. Pass `nil` for each omitted optional argument. |
| `(h3-book-signs-product-sign-theorem lib name formula)` | `(cons step lib)` proving the named product comparison. `name` is an unqualified byte string. |
| `(h3-book-signs-conditional-product-sign lib formula)` | `(cons step lib)` proving the recognized conditional comparison, with `nil` for no match. |
| `(h3-book-signs-rational-product-sign-goal lib target first second orientation)` | `(cons step lib)` proving the rational product sign by the nine combinations of signs. |
| `(h3-book-signs-boolean-comparison-equality lib formula)` | `(cons step lib)` expanding equality of two Boolean comparisons, with `nil` for no match. |

`(h3-book-signs-each-sign lib numeric case arg ...)` is an abbreviation for the three calls to `(case lib signs arg ...)` and their assembly. `case` is an ACL2 function name whose result is `(cons step lib)` or a failure. It is called in positive, zero, negative order. Each callback receives the Library after that sign's evidence is built and after all preceding callbacks. The abbreviation returns `(cons step lib)` or a failure.

`(h3-book-signs-each-sign-prepare lib numeric)` returns `(cons steps lib)`, where `steps` is the list of the positive, zero and negative assumptions. `(h3-book-signs-each-sign-finish lib numeric positive zero negative)` returns the joined Step or a failure. Each of `positive`, `zero` and `negative` is the corresponding callback result Step. These functions allow a caller to use the same sequencing without the abbreviation.

The `-with-library` forms of `negative-reflection`, `sign-evidence`, `each-sign-prepare`, `predicate-value`, `minus-product`, `times-negative-one`, `rational-sign`, `rational-scaling`, `comparison-by-parts`, `scaled-comparison`, `sign-conditions`, `scale-sign-goal`, `product-sign-theorem`, `conditional-product-sign`, `rational-product-sign-goal` and `boolean-comparison-equality` take the same arguments as the calls above. They return `(cons result lib)` on every path. The `result` is the value or failure, and the Library includes auxiliary lemmas registered before a failure.

`h3-book-signs-each-sign-with-library` is an abbreviation with the same syntax as `h3-book-signs-each-sign`. With either abbreviation, a callback that needs to preserve its Library on a failure can return `(cons failure lib)`. The `-with-library` abbreviation returns `(cons result lib)`, including when the result is a failure.

With either abbreviation, a single-element form `(case)` can stand for the callback name. It supplies the callback's own Signs argument before the captured Library, giving `(case signs lib arg ...)`.
