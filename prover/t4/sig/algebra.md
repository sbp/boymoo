# Algebra

`lib` is a Library in the form given in `prover/sig/library.md`. Terms,
symbols and Steps have the forms given in `prover/sig/proof.md`.
`operator` is a prover symbol, usually `BINARY-+` or `BINARY-*` for a
binary operation and `UNARY--` or `UNARY-/` for a unary operation.
`premises` is the ordered list of premise Steps, with `nil` for an
omitted list. A place is a list of indices beginning with the literal
index. Use `:none` when the cancellation factor is absent. A missing Step in a result is `nil`.

The functions in the first table return `(cons value lib)`, with the
Library current after the call, even when the value is a missing Step.
A failure can replace the entire result. The functions in the second
table return their value directly and can return a failure. In both
tables, proof construction can propagate the errors of an inference.

| Call | Value |
|---|---|

| Call | Result |
|---|---|
| `(t4-algebra-fixed lib value typed)` | Equality Step unfolding `FIX` at `value` and selecting the branch proved by `typed`. |
| `(t4-algebra-choose lib equality condition)` | Equality Step selecting the branch of the right side proved by `condition`. |
| `(t4-algebra-commuted lib operator a b)` | Commutativity equality Step for the two operands. |
| `(t4-algebra-associated lib operator a b c)` | Associativity equality Step for the three operands. |
| `(t4-algebra-negative-inverse lib term)` | Equality Step reducing a term plus its negation, with the negation first. |
| `(t4-algebra-value-of test lib step)` | Equality Step assigning the Boolean value of `test` under the signed `step`. |
| `(t4-algebra-equality-tests lib a b forward backward)` | Equality Step for tests `a` and `b`, using the Steps for the two directions. |
| `(t4-algebra-rejected-guard lib guard contrary)` | Step refuting `guard`, or `"search-miss"` when `contrary` refutes none of its conjuncts. |
| `(t4-algebra-inverse-zero lib operator value rejected)` | Equality Step reducing a unary operation on a value that fails its numeric premise. |
| `(t4-algebra-branch-value lib term equation premises)` | Equality Step assigning an equality test its value under the premises, or the original `equation`. |
| `(t4-algebra-element-key term operator)` | The three-element sorting key, using the written term as its string component. |
| `(t4-algebra-operand-at step place)` | The term reached by the indices after the literal index, starting at the first literal of `step`. |
| `(t4-algebra-has-arithmetic term)` | Whether the term contains an arithmetic call outside quotations. Returns a failure for an empty compound. |
| `(t4-algebra-under-operation lib premise template)` | Equality Step applying the same operation to both sides of `premise` using a template with `*proof-result*`. |
| `(t4-algebra-nonzero-fix lib obj rejected)` | The list of the numeric and nonzero Steps for `obj`, in that order. |

`*t4-algebra-fix*` and `*t4-algebra-reciprocal*` are the symbols
`FIX` and `UNARY-/`. `*t4-algebra-operations*` and `*t4-algebra-unit*`
are dictionaries with the addition entry first and the multiplication
entry second. Their values are the operation suffix strings and the
unit terms, respectively.

## Calls to BookLogic

The stateful calls that can request BookLogic operations have
`-with-replies` entry points with a final `replies` argument.
Their `(cons value lib)` result carries the Library even on failure.
`adjacent` and `double-reciprocal-invalid` take the Library directly.
The ordinary calls use an empty reply alist.

A request has the form `(:call kind lib . args)` in the value field.
Reply alists map a full request to a pair `(cons value lib)`. Supply that
pair with the Library after the operation and repeat the original call.
These are the operations, in the forms used by `ordered.lisp`.

| Kind | Arguments | Reply value |
|---|---|---|
| `:arithmetic` | None | `nil`, with arithmetic initialized in the resulting Library. |
| `:fact-proof` | Target term and a fresh Evidence object | The Step, `nil` when the search finds no proof, or a failure. |
| `:constant` | Term | The BookLogic constant equality Step, `nil` when there is none, or a failure. This request covers computations that depend on BookLogic or Ordinals methods. |

`(t4-algebra-query kind lib args replies)` looks up or requests the
operation. `(t4-algebra-interrupted-p value)` recognizes a request or a
failure. `(t4-algebra-constant lib term replies)` returns the constant
equality, request, or failure in a Library result pair.

`(t4-algebra-with-library lib bindings body)` is an abbreviation for
evaluating bindings in order. A binding `(name form)` takes a direct
value. A binding `(name form :library)` takes the value from a result
pair and binds `lib` to the Library in that pair for later bindings and
the body. A request or a failure returns immediately in a Library result
pair.
