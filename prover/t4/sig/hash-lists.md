# Association lists and hashed list operations

`lib` is the Library component of the tactic context, with the form given
in `prover/sig/library.md`. `formula` is a term and the returned Step has
the form given in `prover/sig/proof.md`. `arithmetic` is the Boolean value
of `BookLogic.arithmetic`. `recursive` is the set of recursive function
symbols as a list. These calls use the set only for membership tests.

Each call returns `(cons step new-lib)`. The Step is `nil` when the tactic
does not apply. The Library contains auxiliary definitions and lemmas in
the order in which the tactic adds them. On success the arithmetic flag
becomes `t`. When the Step is `nil`, it retains its input value. A failure
can replace the entire result.

| Call | Result |
|---|---|

BookLogic can run each tactic with its own methods by calling the same
function name with `-query` appended and passing `replies` in place of
`arithmetic`. Requests have the form `(:t4-request operation arguments
lib)`, as in `prover/t4/sig/constructors.md`. The caller starts with `nil`
replies, appends the next reply, and calls again with the original
arguments. Reply values for `:known` and `:fact-proof` are `(cons step
evidence)` and their arguments are `(term evidence)`. `:use-arithmetic`
takes no arguments and has reply value `nil`. `:prove` and `:simplify`
take `(term premises definitions)` and their reply value is the Step or
`nil` when applicable. Each reply is `(cons value lib)` or a failure.

`(t4-hash-lists-query tactic lib formula recursive replies)` runs a tactic
by its keyword, `:put-membership`, `:duplicate-membership`,
`:substitution-map` or `:hash-set-operation`. The result is the same as
the corresponding `-query` function, with `(cons failure lib)` on a
failure so a caller that catches it retains the Library at the failure.

The entry points without `-query` start with no replies. They return
the first request when the tactic needs a BookLogic method. When the
first request is `:use-arithmetic` and `arithmetic` is `t`, the Library
is returned to that operation directly. Run the query entry points to
provide replies to the recipe.

Each `:prove` or `:simplify` operation uses the receiver's constant rules,
including when the recipe proves the shape test of an unfolded list scan.
On a failed method call, a reply of `(cons failure lib)` retains the Library
as of the failure. `(t4-hash-lists-request-p value)` recognizes a request.
