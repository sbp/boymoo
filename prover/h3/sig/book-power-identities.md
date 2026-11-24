# Power identities

`lib` is a Library as specified in `prover/sig/library.md`. Terms and Steps
use the forms in `prover/sig/proof.md`. `context` is a Bounds object as
specified in `prover/h3/sig/book-order.md`. Its evidence is read in insertion order. `*h3-book-power-identities-fix*` and
`*h3-book-power-identities-zip*` are the prover symbols for `FIX` and `ZIP`.

For a call returning `(cons value lib)`, the Library includes auxiliary
lemmas in the order in which they were added. A failure can occupy the value
field and the Library retains the lemmas added before it. For other calls,
a failure is the entire result. A missing optional proof is `nil`.

| Call | Result |
|---|---|
| `(h3-book-power-identities-each-base lib base particular default)` | Request for a callback or `(cons step lib)` joining the three base cases. The callback arguments and results are described below. May fail. |
| `(h3-book-power-identities-base-zero-power lib term fixed-zero)` | Step equating the power term `term` to one or zero according to `ZIP`, using the fixed-base equality Step `fixed-zero`. May fail. |
| `(h3-book-power-identities-power-index-zero lib base)` | Step proving the power with base term `base` and exponent zero equal to one. May fail. |
| `(h3-book-power-identities-power-index-one lib base)` | Step proving the power with base term `base` and exponent one equal to the numeric fix of `base`. May fail. |
| `(h3-book-power-identities-base-one-natural lib index bound)` | `(cons step lib)` proving one raised to the exponent of the integrality Step `index` equals one, using its nonnegative bound Step. May fail. |
| `(h3-book-power-identities-power-base-one lib index)` | `(cons step lib)` proving one raised to the exponent term `index` equals one. May fail. |
| `(h3-book-power-identities-equal-when-both-zero lib base first second summed zeros)` | Step for the addition equation with base term `base` and exponent terms `first`, `second` and `summed`. `zeros` is the list of zero equality Steps, total exponent first and individual exponents in factor order. May fail. |
| `(h3-book-power-identities-addition-with-zero-sum-removed lib base first second first-position summed nonzero-sum fixed)` | `(cons step lib)` for the zero-fixed-base addition equation under a nonzero total. `first`, `second` and `summed` are integrality Steps, `first-position` is the argument index of the first exponent in the sum, and `nonzero-sum` and `fixed` are the nonzero-total and fixed-zero Steps. May fail. |
| `(h3-book-power-identities-signed-zero-indices lib integers zero-sum context nonnegative)` | `(cons steps lib)` containing both individual zero equality Steps in the order of the two integrality Steps in `integers`. `zero-sum` is the total exponent's zero equality Step. `nonnegative` is true when both exponents are nonnegative. May fail. |
| `(h3-book-power-identities-totalized-power-addition lib goal context nonnegative)` | `(cons step lib)` for the addition goal under its Bounds premises. `nonnegative` specifies the common sign when needed. May fail. |
| `(h3-book-power-identities-totalized-power-product lib goal context)` | `(cons step lib)` for the product goal under its Bounds premises. May fail. |
| `(h3-book-power-identities-special-power lib goal)` | `(cons step lib)` for a power equation at a unit base or index, or at a zero base or index. A missing match gives a `nil` Step. May fail. |
| `(h3-book-power-identities-equal-power-zero lib statement)` | Step for the equality between the power's zero test and its totalized condition. May fail. |
| `(h3-book-power-identities-power-is-nonzero lib goal context)` | `(cons step lib)` for the negated zero equality `goal`, or a `nil` Step if no power or matching known proof is found. May fail. |
| `(h3-book-power-identities-reciprocal-power-at-literal lib equation value)` | Step computing the reciprocal of the power in `equation` after rewriting it to the quoted literal `value`. May fail. |
| `(h3-book-power-identities-opposite-power lib base i)` | `(cons step lib)` relating the power at the opposite of exponent term `i` to the reciprocal of the original power with base term `base`. May fail. |
| `(h3-book-power-identities-power-inverse-exponent-theorem lib goal)` | `(cons step lib)` for the recognized reciprocal exponent equation, with a `nil` Step if neither orientation matches. May fail. |
| `(h3-book-power-identities-exponent-sum lib goal context)` | `(cons step lib)` for the recognized exponent addition equation or a `nil` Step when no equation matches. May fail. |
| `(h3-book-power-identities-is-totalized-power-product goal)` | Boolean recognizing the totalized power product equation. A malformed term can fail. |
| `(h3-book-power-identities-power-identities-theorem lib formula)` | `(cons step lib)` for the first matching power identity in `formula`, or a `nil` Step when none applies. May fail. |
| `(h3-book-power-identities-power-default-exponent lib goal context)` | Step for the default power equation under the given Bounds premises, or `nil` when no case applies. May fail. |

## Base callbacks

`each-base` calls the default for a numeric zero base, the particular case
for a nonzero numeric base, and the default for a nonnumeric base, in that
order. A callback result is `(cons step lib)`, with a failure allowed as the
value. The initial `particular` is `nil` and `default` is the list of default
results supplied so far, initially empty. The request has form
`(:h3-power-base-request kind first second lib)`. For `:particular`, `first`
is the numeric Step and `second` is the nonzero Step. For `:default`, `first`
is the fixed-zero equality Step and `second` is the status Step. Supply the
result of the requested callback in `particular` or append it to `default`,
then call `each-base` again with the original Library and base.

`(h3-book-power-identities-with-each-base lib base (particular arg ...)
(default arg ...))` expands the three calls and their assembly. It calls
each named function as `(function current-lib first second arg ...)` with
the corresponding arguments above. The result is `(cons value lib)` as
specified for `each-base`.

`(h3-book-power-identities-with-base-forms live-lib lib base
(typed nonzero) particular-form (fixed status) default-form)` is the same
abbreviation for arbitrary callback forms. Each callback form sees the
current Library bound to `live-lib` and its arguments bound to the two
names preceding that form. Each form returns `(cons value lib)`.
