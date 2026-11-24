# Typed association lists

The `lib` argument is the B1 proof library. Terms, Steps, and the Library use the forms in `prover/sig/proof.md` and `prover/sig/library.md`. Pass evidence as an ordered list of Steps. Each function may return a failure from reading its arguments or constructing a proof. A failure is the entire result.

The symbol constants are `*b1-typed-alists-alist*`, `*b1-typed-alists-domain*`, `*b1-typed-alists-range*`, `*b1-typed-alists-bind*`, `*b1-typed-alists-alist-defun*`, `*b1-typed-alists-alist-cons*`, `*b1-typed-alists-domain-list-rule*`, `*b1-typed-alists-range-list-rule*`, and `*b1-typed-alists-l*`.

| Call | Arguments and result |
|---|---|
| `(b1-typed-alists-alist-body lib items evidence)` | Association-list term `items` and a list of evidence Steps. Returns the `ALIST-TYPE` definition equality with its body reduced. |
| `(b1-typed-alists-alist-parts lib typed cons-step)` | A Step for `ALIST-TYPE` and a Step for `CONSP` on the same list. Returns the Steps for the entry being a cons, its key type, its value type, and the tail's association-list type, in that order. |
| `(b1-typed-alists-empty-alist lib)` | Returns a Step for `ALIST-TYPE` on quoted `NIL`. |
| `(b1-typed-alists-alist-cons lib pair fields)` | A cons term `pair` and Steps for its entry being a cons, key type, value type, and tail type, in that order. Returns the association-list type Step for `pair`. |
| `(b1-typed-alists-alist-type-is-alist lib formula)` | The `ALIST-TYPE-ALISTP` formula. Returns its proof Step. |
| `(b1-typed-alists-alist-type-acons lib formula)` | The association-list type formula for `ACONS`. Returns its proof Step. |
| `(b1-typed-alists-typed-alist-recursion lib formula)` | The association-list type formula for append, bind, remove-binding, restrict-domain, or bind-pairs. Returns its proof Step. |
| `(b1-typed-alists-induction-guard lib tail key value)` | Steps for the tail, key, and value types, respectively. Returns a Step for their conjunction in that order. |
| `(b1-typed-alists-typed-alist-lookup lib formula)` | The `ASSOC-EQUAL` formula for an ill-typed key or for the value type of a successful lookup. Returns its proof Step. |
| `(b1-typed-alists-alist-bound-requires-key lib formula)` | The `ALIST-TYPE-BOUND?-EQUAL` formula. Returns its proof Step. |
| `(b1-typed-alists-range-of-association lib formula)` | The `ALIST-TYPE-CDR-ASSOC-EQUAL` formula, or an instance of it. Returns `(cons step library)` with the proof Step and the Library containing `SELF-RANGE-OF-ASSOCIATION`. The Library adds that lemma at the end of its entries if absent. |
| `(b1-typed-alists-alist-type-binding lib formula)` | The association-list value type formula for `BINDING-EQUAL`. Returns `(cons step library)` with the proof Step and the Library from `b1-typed-alists-range-of-association`. |
| `(b1-typed-alists-alist-projection-type lib formula)` | The `DOMAIN-TYPE` or `RANGE-TYPE` formula for the corresponding projection. Returns its proof Step. |
| `(b1-typed-alists-element-list-fields lib typed cons-step name)` | A list type Step, a cons Step for the typed list, and the symbol naming its list type constraint. Returns the head and tail type Steps, in that order. |
| `(b1-typed-alists-element-list-cons lib head tail name)` | A head type Step, a tail type Step, and the symbol naming the list type constraint. Returns the cons type Step. |
| `(b1-typed-alists-key-type-when-bound lib typed bound)` | An association-list type Step and a `BOUND?-EQUAL` Step. Returns the domain element type Step for the key. |
| `(b1-typed-alists-types-of-bound-entries lib formula)` | The list type formula for `COLLECT-BOUND-EQUAL` or `ALL-BINDINGS-EQUAL`. Returns its proof Step. |
| `(b1-typed-alists-all-bound-requires-keys lib formula)` | The `ALIST-TYPE-ALL-BOUND?-EQUAL` formula. Returns its proof Step. |
| `(b1-typed-alists-paired-alist-type lib formula)` | The association-list type formula for `PAIRLIS$` or `BIND-ALL-EQUAL`. Returns its proof Step. |
