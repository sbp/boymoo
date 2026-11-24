# List type preservation

`library` is the Library component of BookLogic, as described in `prover/sig/library.md`. `recursive` is the set of recursive function symbols as a list without repeats. Only membership in this set is tested. Steps and terms have the forms in `prover/sig/proof.md`. `evidence` is an Evidence object from `prover/t4/sig/structural.md`.

The four theorem tactics return `(cons step library)` on success or `(cons nil library)` when the tactic does not apply. The library in the result includes the entries added during the attempt. Each tactic can return a failure. The `replies` argument for the calls below supplies the results of methods of BookLogic and any external leaf function.

| ACL2 call | Result |
|---|---|
| `(t4-list-types-typed-list-transform library formula recursive replies)` | Result of preserving element types through a cdr traversal that adds typed prefixes. |
| `(t4-list-types-projected-list-type library formula recursive replies)` | Result of proving a type for a field of a recursive result. |
| `(t4-list-types-list-selector-type library formula recursive replies)` | Result of proving a selector's type from a recursive type of its source. |
| `(t4-list-types-append-type library formula recursive replies)` | Result of proving that a recognizer holds for both operands of append, or lifting the recognizer through append. |
| `(t4-list-types-type-of-value library predicate value evidence replies)` | `(list step library evidence)` proving `predicate` of the constructor or known `value`. Requests proofs for nested values through `:nested`. May return a failure. |
| `(t4-list-types-constructor-type library predicate value evidence replies)` | The same result with nested values handled by the constructor typing recipe. May return a failure. |
| `(t4-list-types-cdr-path value object)` | Boolean. True when stripping one or more `CDR` applications from `value` yields `object`. May return a failure on a malformed application. |
| `(t4-list-types-cons-recognizer library predicate pair)` | Equality Step from `constructed-view` for `predicate` of `pair`. May return a failure. |
| `(t4-list-types-in-first library step equality)` | Tidied Step with the first argument of its first literal rewritten by `equality`. May return a failure. |

The constants `*t4-list-types-eq*`, `*t4-list-types-endp*`, `*t4-list-types-acons*`, `*t4-list-types-append*`, and `*t4-list-types-double*` are the prover symbols `EQ`, `ENDP`, `ACONS`, `BINARY-APPEND`, and `DOUBLE-REWRITE`, respectively.

## Method requests

Each call taking `replies` can return a request `(:t4-list-types-request operation library arguments)`. Use `t4-list-types-request-p`, `t4-list-types-request-operation`, `t4-list-types-request-library`, and `t4-list-types-request-arguments` to inspect it. These accessors do not return a failure. Supply the results as an association list of `(request . reply)` entries. Begin with `nil`. For a request, invoke the indicated method with the Library from the request and its ordered arguments, add its reply, and repeat the original call with the augmented alist. A reply is `(list value library evidence)`, with the Library and Evidence from after the method call. For an operation without Evidence, the reply's evidence field is `nil`. The value is a Step, `nil`, or a failure, as returned by the method.

| Operation | Arguments in order | Value |
|---|---|---|
| `:use-arithmetic` | None | `nil` after BookLogic installs its arithmetic lemmas. |
| `:known` | Term, Evidence | Step for known evidence, or `nil`. |
| `:fact-proof` | Term, Evidence | Step from an indexed fact, or `nil`. |
| `:equation` | Term, Evidence | Equality Step for the term, or `nil`. |
| `:nested` | Predicate symbol, value term, Evidence | Step for the predicate of the value, obtained by calling the supplied leaf function. |

## Ordered replies

`(t4-list-types-query recipe library arguments replies)` provides the
same calls for consumers using the ordered request protocol in
`prover/t4/sig/constructors.md`. `recipe` is one of
`:typed-list-transform`, `:projected-list-type`, `:list-selector-type`,
`:append-type`, `:type-of-value`, and `:constructor-type`. `arguments`
contains the arguments between `library` and `replies` in the table
above. Begin with an empty list and append one `(cons value library)`
or failure per request. A request has the form
`(:t4-request operation arguments library)`. For an operation with
Evidence, `value` is `(cons step evidence)`. `:use-arithmetic` has
value `nil`. Final results agree with the corresponding direct calls.

`t4-list-types-query-with-library` takes the same arguments as
`t4-list-types-query`. It keeps the Library in the result when the value
is a failure. The pair `(cons failure library)` lets a theorem tactic
carry the Library into another attempt.

`:prove` takes a term, an ordered list of evidence Steps, and an ordered
list of definitions. It calls BookLogic's proof operation and
returns the resulting Step or failure. This operation has no Evidence
object as an argument. An ordered reply is `(cons step library)` or
`(cons failure library)`. A keyed reply is `(list step library nil)` or
`(list failure library nil)`.
