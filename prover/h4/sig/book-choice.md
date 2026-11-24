# Choice facts

Choice fields are the five-element list of the name, bound variables,
free variables, body and alternate variables of a choice statement.
The variable sequences are in statement order. The free and alternate
variable arguments can be the prover symbol NIL.

| Call | Result and failures |
|---|---|
| `(h4-book-choice-choice-formula fields)` | The term expressing the admitted choice. May return a failure when the fields fail to unpack or substitution fails. |
| `(h4-book-choice-choice-fact p name bindings choices)` | The Step for the instantiated choice. The first argument is a Library. Bindings are two-element lists `(variable term)` in order. Choices are passed separately as an insertion-ordered alist of `(name . fields)` entries. A missing choice produces a failure. Failures from building or instantiating the formula propagate. |
