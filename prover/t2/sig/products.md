# Products and integer order

Libraries, terms, and Steps have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. Each `integers` argument is the list of integer
evidence Steps in supplied order. Pass `nil` for the default `integers`
in `strict-neq` and for the default `weak` in `scale`.

| Function | Arguments and result |
|---|---|
| `(t2-products-times a b)` | Two terms. Returns the product term. |
| `(t2-products-strict-neq lib strict integers)` | Library, strict comparison Step and integer evidence. Returns a Step excluding equality of the operands. |
| `(t2-products-flip-neq lib distinct)` | Library and disequality Step. Returns a Step for the reverse disequality. |
| `(t2-products-strict-from-weak lib bound distinct integers)` | Library, weak comparison Step, disequality Step and integer evidence. Returns the strict comparison Step. |
| `(t2-products-positive-from-nonzero lib)` | Library. Returns the Library with the named lemma available. |
| `(t2-products-multiplication-identities lib)` | Library. Returns the Library with the product negation lemma and its dependencies. |
| `(t2-products-product-zero lib factor)` | Library and factor term. Returns `(cons step lib)` with the product-zero Step and resulting Library. |
| `(t2-products-product-one lib term number)` | Library, factor term and number evidence Step. Returns an equality Step for multiplication by one. |
| `(t2-products-product-difference lib factor upper lower integers)` | Library, factor, upper and lower terms and integer evidence. Returns the distributive equality Step. |
| `(t2-products-product-positive lib a b integers a-positive b-positive)` | Library, two factors, integer evidence and positivity Steps for the factors in order. Returns the product positivity Step. |
| `(t2-products-build-product-order lib)` | Library. Returns the Library with the product comparison lemmas and their dependencies. |
| `(t2-products-scale lib bound positive-factor integers weak)` | Library, comparison Step, factor positivity Step, integer evidence and Boolean selecting a weak comparison. Returns the scaled comparison Step. |
| `(t2-products-cancel-scale lib strict positive-factor integers)` | Library, strict comparison Step, factor positivity Step and integer evidence. Returns the strict comparison Step with the factor canceled. |
| `(t2-products-negate-product lib a b integers)` | Library, two operands and integer evidence. Returns the negation equality Step. |
| `(t2-products-discrete-step lib strict integers)` | Library, strict comparison Step and integer evidence. Returns the weak bound Step with its lower side one unit higher. |

The product constructor cannot fail. Each other function can return a
failure in place of its result when term access or proof construction fails.

The arithmetic helpers below use the Arithmetic rule when the Library's
Proof has kind `:slice`. Every call can return a failure.

| Function | Arguments and result |
|---|---|
| `(t2-products-library-type-of lib term evidence)` | Library, term and integer evidence. Returns the integer Step for the term. |
| `(t2-products-library-natural lib term)` | Library and term. Returns its naturalness Step. |
| `(t2-products-library-modus-ponens lib step evidence)` | Library, implication Step and premise Step. Returns the consequent Step. |
| `(t2-products-library-rational lib term evidence)` | Library, term and integer evidence. Returns the rationality Step. |
| `(t2-products-library-number lib term evidence)` | Library, term and integer evidence. Returns the ACL2 number Step. |
| `(t2-products-library-comparison lib a b integers)` | Library, comparison operands and integer evidence. Returns the equality with positivity of the difference. |
| `(t2-products-numeric-add-zero lib number)` | Library and number evidence Step. Returns the left addition identity Step. |
| `(t2-products-unique-inverse lib value candidate zero candidate-number)` | Library, operand and proposed inverse, zero-sum Step and number Step for the candidate. Returns the equality of the negated operand and candidate. |
| `(t2-products-library-linear-equal lib left right integers)` | Library, terms and integer evidence. Returns the equality Step from the terms' common linear form. |
| `(t2-products-library-weak-from-difference lib a b difference integers)` | Library, terms, Step proving the difference nonnegative, and integer evidence. Returns the weak comparison Step. |
