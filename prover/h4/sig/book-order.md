# Ordinal order proofs

`p` is an H4 `Tactics` library as specified in `prover/h4/sig/tactics.md`. Terms, symbols, clauses and Steps use the forms in `prover/sig/proof.md`. An evidence argument is an ordered list of Steps. A shape is a Step for `CONSP` of a subject or for its negation. A missing match or Step is `nil`. All proof operations can return a failure in place of the stated result.

The constants `*h4-book-order-finite*`, `*h4-book-order-exponent*`, `*h4-book-order-coefficient*` and `*h4-book-order-rest*` denote the ordinal selectors `O-FINP`, `O-FIRST-EXPT`, `O-FIRST-COEFF` and `O-RST`. `*h4-book-order-selectors*` lists the last three in that order. `*h4-book-order-obasics*` lists `O-FINP`, `ATOM`, `=` and `NOT`. `*h4-book-order-boolean*`, `*h4-book-order-fix*`, `*h4-book-order-posp*`, `*h4-book-order-ocmp*`, `*h4-book-order-omega*`, `*h4-book-order-omega-term*` and `*h4-book-order-make-ord*` denote the corresponding prover symbols. `*h4-book-order-order-self*`, `*h4-book-order-order-bool*`, `*h4-book-order-order-trans*`, `*h4-book-order-order-ties*` and `*h4-book-order-order-origin*` denote the support fact names in order of construction.

## Shared proof operations

| ACL2 call | Result |
|---|---|
| `(h4-book-order-primitive-transitive p first second)` | Step composing two primitive strict comparisons. |
| `(h4-book-order-primitive-reflexive-value p argument)` | Equality Step for `(< argument argument)` with value quoted `NIL`. |
| `(h4-book-order-order-view p atom evidence expand)` | Equality Step unfolding `atom` and normalizing with the supplied evidence and definitions. Pass `nil` for either optional list. |
| `(h4-book-order-false-value p equality)` | Step negating the left side of an equality to quoted `NIL`. |
| `(h4-book-order-order-unequal p strict reflexive)` | Step for unequal endpoints of the strict comparison. The last argument represents the reflexivity function as described below. |
| `(h4-book-order-ordinal-induction p formula subjects build)` | Induction Step for `formula` on the ordinal count of the first subject, with exponent and tail substitutions. The last argument represents the case builder as described below. |
| `(h4-book-order-reflected-test p test)` | Step reversing the operands of an equality or negated equality. |
| `(h4-book-order-ordinal-components p proof shape)` | Alist mapping each literal to its Step, in conjunct order, from an ordinality Step for a cons of the given shape. Repeated literals keep their first position and last Step. |
| `(h4-book-order-strict-chain p first second)` | Step composing two strict ordinal comparisons using the transitivity fact. |
| `(h4-book-order-true-order-value p positive)` | Equality Step that the strict ordinal comparison proved by `positive` has value quoted `T`. |
| `(h4-book-order-true-boolean-value p positive boolean)` | Equality Step that the proposition in `positive` has value quoted `T`, using its Boolean type Step. |
| `(h4-book-order-order-formula p formula evidence)` | Step for a conjunction or elementary order relation, or `nil`. |
| `(h4-book-order-order-support p)` | `(cons support p)` with the resulting library and an ordered alist from support names to clauses. The order is self-comparison, Boolean comparison, transitivity, equality from order and the origin bound. |
| `(h4-book-order-ordinal-proof p formula support)` | Step for `formula`, or `nil`, using the supplied support alist. |

`reflexive` in `order-unequal` receives the comparison's right operand. Pass `:primitive` to call `primitive-reflexive-value`, `:ordinal` to cite `ORDER_SELF` with `X` bound to the operand, `(:instantiate step)` to instantiate a supplied Step with that binding, or `(:result step-or-failure)` with the result of another function for that operand.

`build` in `ordinal-induction` is a list of successive case replies, each a Step or failure. With an empty reply list, the call returns `(:call :ordinal-induction shape child)` for the cons case after producing the selector hypotheses. `child` is an alist from selector symbols to their hypothesis Steps, in exponent and tail order. Evaluate the case builder on `shape` and `child` and repeat with the reply appended. The second request is for the atom case, with a `nil` child alist. The final call uses both replies in order. `h4-book-order-ordinal-induction-request-p` takes any value and recognizes these requests.

## Formula recognition

| ACL2 call | Result |
|---|---|
| `(h4-book-order-comparison-equality formula)` | The two subjects if `formula` relates an `OCMP` tag to the corresponding order, or `nil`. |
| `(h4-book-order-relation-atom term)` | The operand of `NOT` or the term itself. |
| `(h4-book-order-elementary-relation term)` | Boolean recognizing ordinal order, ordinality or equality with elementary arguments. |
| `(h4-book-order-boolean-order-equality formula)` | Boolean recognizing equality between a strict ordinal comparison and a negated equality. |
| `(h4-book-order-selector-comparison formula)` | Subject list for a comparison on ordinal fields, or `nil`. |
| `(h4-book-order-ordinal-candidate formula)` | Boolean recognizing a candidate for the order tactic. |
| `(h4-book-order-selector-type formula)` | Matching subject in a formula about the type of an ordinal field, or `nil`. |
| `(h4-book-order-selector-count formula)` | `(subject selector path)` for strict descent into an ordinal field, or `nil`. |
| `(h4-book-order-omega-comparison formula)` | Matching subject in a comparison with `OMEGA`, or `nil`. |

The recognizers can return a failure for malformed applications.

## Order proof construction

| ACL2 call | Result |
|---|---|
| `(h4-book-order-sum-number p term)` | Step for the numeric type of a sum or negation. |
| `(h4-book-order-zero-plus p term)` | Equality Step for the left additive identity on `term`. |
| `(h4-book-order-sum-differences p first middle last)` | Equality Step cancelling the common term in two differences. |
| `(h4-book-order-positive-difference p low high)` | Equality Step expressing a strict comparison as positivity of a difference. |
| `(h4-book-order-self-order-value p)` | Step for irreflexivity of ordinal comparison. |
| `(h4-book-order-selector-hypotheses p formula subjects shape)` | Alist from the exponent and tail selectors, in that order, to induction hypothesis Steps. |
| `(h4-book-order-boolean-order p)` | Step for the Boolean type of an ordinal comparison. |
| `(h4-book-order-transitive-order p)` | Step for transitivity of ordinal comparison. |
| `(h4-book-order-finite-equal p left right no-forward no-backward integers)` | Equality Step for two integers with neither strict comparison. `integers` is the ordered list of integer type Steps. |
| `(h4-book-order-reconstruct-ordinal p term shape head-shape)` | Equality Step reconstructing a cons ordinal from its fields. |
| `(h4-book-order-equal-when-unordered p)` | Step for equality of two ordinals with neither strict comparison. |
| `(h4-book-order-origin-bound p)` | Step proving the origin is a lower bound for all ordinals. |
| `(h4-book-order-from-ordinal-origin p proof)` | Step applying the origin bound to an ordinality Step. |
| `(h4-book-order-selector-types-proof p formula subject)` | Step for the matched selector type formula. |
| `(h4-book-order-selector-count-proof p formula match)` | Step for the matched selector descent formula. |
| `(h4-book-order-positive-lower-bound p positive integral)` | Step applying discreteness to a positive integer. |
| `(h4-book-order-nonzero-ordinal-lower-bound p ordinal nonzero)` | Step bounding a nonzero ordinal from below by one. |
| `(h4-book-order-omega-comparison-proof p formula subject)` | Step for the matched comparison with `OMEGA`. |
| `(h4-book-order-selector-order-proof p formula subjects)` | Step for the matched selector comparison, or `nil` when the proof fails with `unproved`. |
| `(h4-book-order-ocmp-proof p formula subjects)` | Step for the matched equality between an `OCMP` tag test and ordinal order. |
| `(h4-book-order-order-value-equality p formula evidence)` | Step for the matched equality of order and Boolean values, or `nil`. |

## Consequences

An `OrdinalConsequences` object has the form `(:h4-book-order-ordinal-consequences p goal literals terms conflict)`. Its `literals` alist maps first literals to Steps in insertion order. The initial evidence assigns the last Step to a repeated key without moving it. Subsequent additions retain the first Step. `terms` lists distinct arguments of the relation atoms, traversing the goal before the initial literals and using first occurrence order. `conflict` is the first contradiction Step, or `nil`.

| ACL2 call | Result |
|---|---|
| `(h4-book-order-ordinal-consequences-init p goal evidence)` | Initialized `OrdinalConsequences` object. |
| `(h4-book-order-ordinal-consequences-add object proof)` | Resulting object after adding the Step if its first literal is new. |
| `(h4-book-order-ordinal-consequences-between object a b c)` | Resulting object after adding transitivity consequences. |
| `(h4-book-order-ordinal-consequences-transfer object a b)` | Resulting object after adding the equality consequences for these terms. |
| `(h4-book-order-ordinal-consequences-solve n object)` | `(cons step object)` with the resulting object and the Step or `nil`. Pass `1000000` for initial natural-number fuel. May return `fuel` in addition to proof failures. |
