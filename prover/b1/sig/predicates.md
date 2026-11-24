# Boolean list predicates

`*b1-predicates-booleanp*` is the term symbol for `ACL2::BOOLEANP`.

`(b1-predicates-boolean-definition lib call slot)` takes a Library, a call
term, and the one-based argument position of the list being traversed. It
returns `(cons step lib)` with the Boolean type step and the Library after
any auxiliary lemma is added. It can return a failure for a missing
definition, malformed call, non-Boolean leaf, or failure to construct the
proof. It examines conditional branches in order, visiting the true branch
before the false branch. Bindings follow the order of the definition's
formals.
