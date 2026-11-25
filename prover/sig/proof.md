# Proofs and proof steps

`prover/proof.lisp` holds the theory that a proof is made in, the steps of a proof with the eight rules that make them, and the text of a finished proof. The rules made of these are in `prover/proof2.lisp` (`prover/sig/proof2.md`). A function that cannot give its value gives a failure in its place (`prover/FAILURES.md`); the tables name the kinds.

## Terms and data

Data have the forms of `prover/sig/reader.md`: an integer, or a list that begins with a string tag, as in `("sym" "ACL2" "X")` for the symbol `ACL2::X` and `("str" "equal-same")` for a string, or a list of data. The empty list is `nil`.

A term is a datum: a variable is a symbol, a constant is the list of `*proof-quote*` and a datum, a call is the list of a function's symbol and its arguments, and a lambda application is the list of its lambda and its actuals, the lambda being the list of the symbol `COMMON-LISP::LAMBDA`, the list of formals and the body. A literal is a term. A clause is a list of literals, and says that one of them holds. The name of a fact is a symbol or a string datum.

| Call | Value |
|---|---|
| `(proof-sym name package)` | The symbol of the two strings. |
| `(proof-cl name)` | The symbol of the string `name` in the package `"COMMON-LISP"`. |
| `(proof-quote datum)` | The constant of the datum. |
| `(proof-eq left right)` | The term `(EQUAL left right)`. |
| `(proof-neg term)` | The term `(NOT term)`. |
| `(proof-ite test yes no)` | The term `(IF test yes no)`. |
| `(proof-compound datum)` | Whether the datum is a list of data: `nil`, or a list that does not begin with a string. |
| `(proof-is-call term head)` | Whether the term is a list of data that is not empty and begins with `head`. |
| `(proof-all-quoted-p terms)` | Whether every term of the list is a constant. |
| `(proof-freeze datum)` | The datum itself. |
| `(proof-thaw datum)` | The datum as the writer takes it: every `nil` in it becomes the symbol `*proof-nil*`. Failure `"index"` for a dotted tail without its datum. |
| `(proof-unique items)` | The items in the order in which each first occurs, without the repeats. |

The symbols `*proof-nil*`, `*proof-t*`, `*proof-quote*`, `*proof-if*`, `*proof-equal*`, `*proof-not*`, `*proof-cons*`, `*proof-consp*`, `*proof-integerp*` and `*proof-less*` (`<`) are in the package `COMMON-LISP`. `*proof-plus*` (`BINARY-+`), `*proof-times*` (`BINARY-*`), `*proof-minus*` (`UNARY--`), `*proof-ordinalp*` (`O-P`), `*proof-ordinal-less*` (`O<`) and `*proof-result*` (`SELF-RESULT`) are in the package `ACL2`. The constants `*proof-false*`, `*proof-true*`, `*proof-zero*`, `*proof-one*` and `*proof-neg-one*` are the terms `'NIL`, `'T`, `'0`, `'1` and `'-1`.

## The Proof

A Proof is `(:proof facts definitions primitives)`, the theory in which steps are made.

- `facts` is a table (`prover/sig/basics.md`) from the names of facts to their clauses.
- `definitions` is a table from the symbols of functions to `(formals body)`.
- `primitives` is the list of the symbols of the primitive functions.

A Proof may have a fifth member, its kind, `:slice` or `:book`. A Proof without one is of the kind `:base`. The kind chooses among the forms of three rules of `prover/sig/proof2.md`, and every function below that returns a Proof keeps it.

| Call | Value |
|---|---|
| `(proof-make-proof facts definitions primitives)` | The Proof of the three members, of the kind `:base`. |
| `(proof-proof-init)` | The Proof of the ground theory: the facts, definitions and primitives of `spec/ground.txt`, which the book holds as the constant `*proof-ground*`. |
| `(proof-proof-facts proof)` | The facts. |
| `(proof-proof-definitions proof)` | The definitions. |
| `(proof-proof-primitives proof)` | The primitives. |
| `(proof-proof-kind proof)` | The kind. |
| `(proof-proof-with-facts proof facts)` | The Proof with the given facts. |
| `(proof-proof-with-kind proof kind)` | The Proof with the given kind. |
| `(proof-proof-add-definition proof name formals body)` | The Proof with the definition of `name`, and with the fact of that name whose clause is the one literal `(EQUAL (name formal ...) body)`. Formals given as `*proof-nil*` are no formals. |

## The Step

A Step is `(:step word data clause)`: `clause` is what has been proved, `word` is the string that names the rule that proved it, and `data` is the list of what the rule was given. A member of `data` that is a Step is a premise. A Step so holds the whole proof of its clause. The first literal of the clause is the one that the rules work on, and the others are its side literals.

| Call | Value |
|---|---|
| `(proof-make-step word data clause)` | The Step of the three members. |
| `(proof-step-p value)` | Whether the value is a list of four members that begins with `:step`. |
| `(proof-step-word step)` | The word. |
| `(proof-step-data step)` | The data. |
| `(proof-step-clause step)` | The clause. |
| `(proof-step-first step)` | The first literal of the clause. Failure `"index"` for an empty clause. |

## Substitutions and places

Bindings that a rule takes are a list of two-member lists `(variable term)`. A substitution that is applied is a table with entries `(variable . term)`. A place in a term is the list of the numbers of the arguments that lead down to a subterm, from 1. A place in a Step begins with the number of a literal of its clause, from 1.

| Call | Value | Failure |
|---|---|---|
| `(proof-subst term bindings)` | The term with each variable that is a key of the table `bindings` replaced by its value. Nothing is replaced in a constant or in a lambda. | `"index"` for an empty list among the subterms. |
| `(proof-subst-arguments terms bindings)` | The list of the terms, each so substituted. | The same. |
| `(proof-bindings-table pairs bindings)` | The table `bindings` after `table-put` of each `(variable term)` of the list `pairs`. | None. |
| `(proof-nonidentity-pairs bindings)` | The members of a list of bindings that do not give a variable itself. | `"value"` for a member that does not have two members. |
| `(proof-change term place old new)` | The term with `new` at the place, where `old` must stand. | `"assertion"` when another term stands there, and when the place leads into a constant, a variable or past the arguments. `"index"` for an empty list on the way. |
| `(proof-without-literal clause literal)` | The clause without the literal. | None. |

## The rules

Each rule returns a Step. Its word and data are those of the step lines of `spec/formats.md`, section 6. `proof` is a Proof, `step` and the other premises are Steps, and bindings are as above, with `nil` for none.

| Call | Value | Failure |
|---|---|---|
| `(proof-proof-fact proof name bindings)` | The fact of that name, instantiated with the bindings. A name given as an ACL2 string stands for the string datum. | `"key"` when there is no such fact, and those of `proof-proof-instantiate`. |
| `(proof-proof-instantiate proof step bindings)` | The Step with the bindings applied to its clause. Bindings of a variable to itself are dropped, and when none is left the value is `step` itself. | `"value"` for a binding that does not have two members. `"assertion"` when a variable is bound twice. Those of `proof-subst`. |
| `(proof-proof-subsume proof step clause)` | A Step with the given clause, when every literal of the clause of `step` is `'NIL` or is in it. The value is `step` itself when the clauses are equal. | `"assertion"` otherwise. |
| `(proof-proof-tidy proof step)` | The Step without its literals `'NIL` and without repeated literals. | Those of `proof-proof-subsume`. |
| `(proof-proof-front proof step literal)` | The Step with `literal` first and nowhere else. | `"assertion"` when the literal is not in the clause. |
| `(proof-proof-cut proof positive negative)` | From `positive`, whose first literal is `P`, and `negative`, whose first literal is `(NOT P)`: the Step of the other literals of the two, tidied. | `"assertion"` when the first literals do not fit so. `"index"` for an empty clause. |
| `(proof-proof-rewrite proof step equality place)` | The Step with the right side of the equality at the place, where the left side must stand. `equality` is a Step whose first literal is `(EQUAL left right)`, and its side literals are added at the end of the clause. | Those of `proof-change`, `"assertion"` when the first literal of `equality` is not an equality, `"index"` when the place names no literal. |
| `(proof-proof-rewrite-result proof step equality template slot)` | The Step rewritten with the equality at each place where the term `slot` stands in the term `template`, taken as the first literal, and then tidied. The usual slot is `*proof-result*`. | Those of `proof-proof-rewrite`. |
| `(proof-proof-rewrite-first proof step equality)` | The Step rewritten with the equality wherever its left side stands in the first literal, and then tidied. | Those of `proof-proof-rewrite`. |
| `(proof-proof-beta proof term)` | The Step of `(EQUAL term body')` for a lambda application `term`, `body'` being the body with the formals replaced by the actuals. | `"value"` when `term` is empty or its head is not a list of three members. |
| `(proof-proof-compute proof term value)` | The Step of `(EQUAL term 'value)` for a call of a primitive on constants. `value` is the datum of the value, which the caller has computed. | `"assertion"` when the head is not a primitive or an argument is not a constant. |
| `(proof-proof-induct proof ordinal case formula measure substitutions)` | The Step of the clause `(formula)`, by induction on `measure`. `ordinal` is a Step whose clause is the one literal `(O-P measure)`. `substitutions` is a list of lists of bindings, one for each smaller instance. `case` is a Step whose literals are among `formula` and, for each of the substitutions `s`, the literal `(NOT (IF (O< measure/s measure) formula/s 'T))`. | `"assertion"` when `ordinal` or `case` does not fit, and those of `proof-subst`. |
| `(proof-proof-induct-hypothesis pairs formula measure)` | That literal for one list of bindings `pairs`. | Those of `proof-subst`. |

Two functions use the rules on a fact and its premises:

| Call | Value | Failure |
|---|---|---|
| `(proof-discharge proof step evidence)` | The Step without one side literal, which the Step `evidence` settles: the first literal of `evidence` is the negation of the side literal, or the side literal is the negation of it. The first literal of `step` stays first, and the side literals of `evidence` join the clause. When the clause of `evidence` is only its first literal and that side literal, the value is `step` itself. | `"value"` when no side literal fits, with the texts of the literals in the message. |
| `(proof-proof-use proof name bindings evidence)` | The fact of that name, instantiated, and then discharged with each Step of the list `evidence` in order. A Step whose first literal an earlier one had is passed over. | Those of `proof-proof-fact` and `proof-discharge`. |

## The text of a proof

| Call | Value | Failure |
|---|---|---|
| `(proof-write datum)` | The text of the datum (`prover/sig/reader.md`), after `proof-thaw`. | `"index"`, from `proof-thaw`. |
| `(proof-write-list data)` | The list of the texts of the data. | The same. |
| `(proof-line word data)` | The line `(word datum ...)` of the string `word` and the list `data`, with its line feed. | The same. |
| `(proof-serialize last)` | The list of the step lines of the proof that ends in the Step `last`. A premise is written as the number of its line, lines are numbered from 1 in the order in which they are first needed, and a line that is equal to an earlier one is not written again. | `"attribute"` when `last` is not a Step, and those of `proof-line`. |
| `(proof-proof-entry kind name fields proofs)` | The list `(kind name counts text)` of an entry of a proof file: `text` is the head line `(kind field ...)` and then, for each Step of the list `proofs`, its step lines and the line `(qed)`; `counts` is the list of the numbers of step lines. | Those of `proof-serialize`. |
| `(proof-emitted-lines emitted lines)` | The keys of the table `emitted`, last first, before the list `lines`. `proof-serialize` keeps its lines in such a table, the newest first. | None. |

## Failures of form

| Call | Value |
|---|---|
| `(proof-index-failure)` | The failure `(:failure "index" "")`, for a member that a list does not have. |
| `(proof-length-failure expected found)` | A failure of the kind `"value"` for a list of `found` members where `expected` were wanted. The message gives the numbers. |
| `(proof-datum-text datum)` | The text of a datum in the message of a failure: its members between parentheses with `, ` between them, the strings in it written with `text-quoted`. |
