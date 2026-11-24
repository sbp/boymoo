# The obligations of a definition

The signatures are in `prover/sig/termination.md`.

The book proves nothing. It reads the definitions of a `define` line and writes the clauses that a proof of termination has to end in; `prover/descent.lisp` and the tactics prove them.

## Rulers

The tests of a Call are the conditions under which the call is reached, and they become the hypotheses of its obligation. They are collected from the `IF`s that rule a call, and the ruler extenders of the definition say how far into the arguments of other functions and of lambdas an `IF` still rules. The rule is the one that `spec/logic.md` gives under `define` in its section 6, where the obligations of termination that a checker asks for are defined; `prover/sig/termination.md` lists the positions as the book reads them.

The actuals and the tests of a Call are written in the caller's formals. Inside a lambda the walk carries a table from the lambda's formals to their actuals and applies it to what it records, so no variable of a lambda is left in a Call.

`(RETURN-LAST 'MBE1-RAW a b)` is how an `mbe` reaches the books, and its logical value is `b`. The walk reads `b` alone, and `termination-logical-body` makes the same replacement in a whole term.

## Cases and clauses

`termination-obligation-cases` keeps each clause with the Call it came from, so a tactic can choose a recipe by the shape of the call. `termination-obligations` gives the same clauses, each once, in the order of the cases. That is the list for a proof file, where the entry `(measure F M1 ... Mk)` is followed by one proof for each obligation in order (`spec/formats.md`, section 6).

## The selector plan

`termination-selector-plan` answers one question: can each function of the definition be measured by the size of one of its formals, every call taking `CAR`s and `CDR`s of the caller's formal? It tries every choice of one formal a function, so its work is the product of the numbers of formals; the counter of 1,000,000 bounds it.

## Finding only whether there is a call

`termination-recursive-calls` reads every definition to its end. A caller that needs only to know whether a definition is recursive has a function of its own that stops at the first call: `book-proofs-recursive-call-p` of `prover/book-proofs.lisp`, which decides the ruling positions with `termination-recursive-calls-extends` as this book does.
