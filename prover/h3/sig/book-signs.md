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
| `(h3-book-signs-zero-contradiction lib term index sign)` | Step disproving equality to zero using the strict comparison Step `sign` and the given rewrite index. |
| `(h3-book-signs-rational-product lib ra rb)` | Step proving the product of the two rational arguments rational. |
| `(h3-book-signs-scaled-parts lib term scalar-type)` | List of two Steps for the real and imaginary parts of the scaled term, with the real part first. |
| `(h3-book-signs-nonnumeric-signs lib term absent)` | List of Steps for the two default order comparisons followed by denial of equality to zero. |

`(h3-book-signs-each-sign lib numeric case arg ...)` is an abbreviation for the three calls to `(case lib signs arg ...)` and their assembly. `case` is an ACL2 function name whose result is `(cons step lib)` or a failure. It is called in positive, zero, negative order. Each callback receives the Library after that sign's evidence is built and after all preceding callbacks. The abbreviation returns `(cons step lib)` or a failure.

The `-with-library` forms of `negative-reflection`, `sign-evidence`, `each-sign-prepare`, `predicate-value`, `minus-product`, `times-negative-one`, `rational-sign`, `rational-scaling`, `comparison-by-parts`, `scaled-comparison`, `sign-conditions`, `scale-sign-goal`, `product-sign-theorem`, `conditional-product-sign`, `rational-product-sign-goal` and `boolean-comparison-equality` take the same arguments as the calls above. They return `(cons result lib)` on every path. The `result` is the value or failure, and the Library includes auxiliary lemmas registered before a failure.

`h3-book-signs-each-sign-with-library` is an abbreviation with the same syntax as `h3-book-signs-each-sign`. With either abbreviation, a callback that needs to preserve its Library on a failure can return `(cons failure lib)`. The `-with-library` abbreviation returns `(cons result lib)`, including when the result is a failure.

With either abbreviation, a single-element form `(case)` can stand for the callback name. It supplies the callback's own Signs argument before the captured Library, giving `(case signs lib arg ...)`.
