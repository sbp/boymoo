# List algebra

A Library and a Step have the forms in their respective signatures. A term is
a prover term. The constants `*list-algebra-associative*` and
`*list-algebra-associativity*` are the append associativity lemma's name
string and formula.

Each function below returns `(cons result library)`, with the Library as it
stands on return. A completed result can be a failure. `nil` means the
tactic supplied no proof.

| Function | Arguments in order | Result |
| --- | --- | --- |
| `list-algebra-append-associativity` | Library, first term, second term, last term | Step instantiating append associativity |
| `list-algebra-list-algebra` | Library, formula term | Step proving the formula, `nil`, or a request |
| `list-algebra-list-algebra-resume` | Library, continuation, answer | Step proving the formula |

A request is `(:call goal evidence continuation)`. The caller proves
`goal` using the evidence Steps and passes the Step or failure as
`answer` together with the resulting Library. Pass the continuation
as returned.
