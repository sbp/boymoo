# The obligations of a definition

`prover/termination.lisp` finds the calls by which the functions of a definition call one another, and writes what has to be proved for the definition to be admitted with given measures. Terms and symbols have the forms of `prover/sig/proof.md`. A failure (`prover/FAILURES.md`) takes the place of a value; the last column names the kinds.

## Forms

- A **definition** is `(name formals body)`. The functions that are defined together are a list of definitions, as a `define` line gives them (`spec/formats.md`).
- The **ruler extenders** of a `define` line are its first datum: the symbol `KEYWORD::ALL`, or a list of symbols.
- A **signed test** is `(term holds)`: `holds` is `t` when the term is true where the test applies, and `nil` when it is false.
- A **Call** is `(caller callee actuals tests)`: the symbols of the calling and the called function, the list of the actual arguments, and the list of the signed tests that rule the call, from the outermost. The actuals and the tests are written in the formals of the caller: the variables of the lambdas around the call are replaced by what they are bound to.
- **Measures** are a table (`prover/sig/basics.md`) with entries `(name . measure)`.

| Call | Value |
|---|---|
| `(termination-make-call caller callee actuals tests)` | The Call of the four members. |
| `(termination-call-caller call)` | The caller. |
| `(termination-call-callee call)` | The callee. |
| `(termination-call-actuals call)` | The actuals. |
| `(termination-call-tests call)` | The signed tests. |

The constants are the symbols `*termination-all*` (`KEYWORD::ALL`), `*termination-lambdas*` (`KEYWORD::LAMBDAS`) and `*termination-return-last*` (`ACL2::RETURN-LAST`), the term `*termination-mbe*` (`'ACL2::MBE1-RAW`), and `*termination-selectors*`, the list of the symbols `CAR` and `CDR`.

## The calls and the obligations

| Call | Value | Failure |
|---|---|---|
| `(termination-logical-body term)` | The term with every `(RETURN-LAST 'MBE1-RAW a b)` in it replaced by `b`, also in the bodies of lambdas. | `"index"` for a call that lacks a member. |
| `(termination-recursive-calls rulers definitions)` | The list of the Calls of the definitions to one another, for the ruler extenders `rulers`: definition by definition, and in a body in the order of reading, a call before the calls among its arguments. | `"index"`, `"value"` or `"type"` for a definition or a term that lacks a member. |
| `(termination-obligation-cases definitions measures calls)` | The list of the cases `(clause call)`. First, for each definition, the clause of the one literal `(O-P measure)`, with `nil` for the call. Then, for each Call, the clause of its tests and of `(O< smaller measure)`, where `measure` is that of the caller and `smaller` that of the callee with the actuals in the place of its formals. A test that holds is written `(NOT term)` in the clause, and one that does not is written `term`. | `"key"` when a function has no measure or no definition, with the text of its name. Those of `proof-subst`. |
| `(termination-obligations definitions measures calls)` | The clauses of those cases, each once, in the order in which it first occurs. | The same. |
| `(termination-selector-plan definitions calls)` | A table `(name . formal)` that gives each function one of its formals, such that in every Call the actual in the place of the callee's formal is one or more of `CAR` and `CDR` applied to the caller's formal. `nil` when there is no such choice, and when a function has no formals. The choices are tried in the order of the formals, those of the last function changing first, and the first that fits is the value. | `"fuel"`, and `"key"` or `"index"` for a Call that does not fit the definitions. |

`termination-recursive-calls` reads a body so:

- A variable or a constant has no calls.
- In `(RETURN-LAST 'MBE1-RAW a b)` only `b` is read.
- An `IF` in a ruling position gives the calls of its test, then those of its true branch under the test signed `t`, then those of its false branch under the test signed `nil`. The branches are ruling positions.
- A lambda application gives the calls of its actuals and then those of its body, in which the formals stand for the actuals. The body is a ruling position when the application is.
- Any other call gives itself, when it is of one of the functions defined, and then the calls of its arguments.
- The body of a definition is a ruling position. The arguments of a call of `f`, the test of an `IF`, and the actuals of a lambda are ruling positions only when the call is in one and the ruler extenders are `KEYWORD::ALL` or have `f`, `IF` or `KEYWORD::LAMBDAS` among them. An `IF` that is not in a ruling position is read as any other call and adds no test.

## Parts that other books call

| Call | Value |
|---|---|
| `(termination-recursive-calls-extends name rulers)` | Whether `rulers` is `KEYWORD::ALL` or a list that has `name`. |
| `(termination-definition-names definitions)` | The list of the names of the definitions. |
| `(termination-formals definitions normalize formals)` | The table `formals` with the entry `(name . formals)` of each definition put. When `normalize` is `t`, formals given as `*proof-nil*` are `nil`. |
| `(termination-subst-actuals terms env)` | The list of the terms with the table `env` applied by `proof-subst`. |
| `(termination-lambda-bindings formals actuals env bindings)` | The table `bindings` with each formal put with its actual, `env` applied to the actual. |
| `(termination-bindings formals actuals bindings)` | The table `bindings` with each formal put with its actual. |
| `(termination-ordinality-cases definitions measures)` | The first cases of `termination-obligation-cases`, those of `(O-P measure)`. |
| `(termination-call-cases calls measures formals)` | Its other cases, those of the Calls. `formals` is a table of `termination-formals`. |
