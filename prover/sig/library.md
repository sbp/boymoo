# The library of lemmas

`prover/library.lisp` holds the Library, a Proof together with the lemmas and definitions that have been added to it, the rules that cite them, and the first lemmas: logic, the integers and sums. `prover/library2.lisp` builds the rest (`prover/sig/library2.md`). Terms, the Proof and the Step have the forms of `prover/sig/proof.md`. Every function that makes a Step or adds to a Library can return a failure in place of its value (`prover/FAILURES.md`).

## The Library

A Library is `(:library proof entries)`. `proof` is a Proof. `entries` is the list, in the order of adding, of what the Library has added to the ground theory, as it is written in a proof file. An entry is `(kind name counts text)`:

- for a lemma, `("lemma" name (count) text)`: `text` is the head line `(lemma name claim condition ...)`, the step lines of the proof and the line `(qed)`, and `count` is the number of step lines;
- for a definition, `("define" name nil text)`: `text` is the line `(define COMMON-LISP::NIL (name formals body))`.

`name` is a symbol. A lemma that is given the name `N`, a string, is the fact of the symbol `ACL2::SELF-N`, and it is cited by `N`.

| Call | Value |
|---|---|
| `(library-make-library proof entries)` | The Library of the two members. |
| `(library-library-init proof)` | The Library of the Proof with no entries. |
| `(library-library-proof library)` | The Proof. |
| `(library-library-entries library)` | The entries. |
| `(library-library-with-proof library proof)` | The Library with the given Proof and its own entries. |
| `(library-library-with-entries library entries)` | The Library with its own Proof and the given entries. |
| `(library-lemma-name name)` | The symbol `ACL2::SELF-name` of the string `name`. |

A rule of `prover/sig/proof.md` or `prover/sig/proof2.md` takes `(library-library-proof library)` as its Proof. The macro `(library-inherited rule library argument ...)` writes that call: it is `(rule (library-library-proof library) argument ...)`.

## Terms

`*library-x*`, `*library-y*` and `*library-z*` are the variables `ACL2::X`, `ACL2::Y` and `ACL2::Z`, the variables of every lemma. The other constants are symbols of functions: `*library-natp*`, `*library-numberp*` (`ACL2-NUMBERP`), `*library-o-finp*`, `*library-count*` (`ACL2-COUNT`), `*library-len*`, `*library-implies*`, `*library-nfix*` (`SELF-NFIX`) and `*library-gap*` (`SELF-GAP`) in the package `ACL2`, and `*library-car*`, `*library-cdr*` and `*library-rationalp*` in `COMMON-LISP`.

| Call | Value |
|---|---|
| `(library-plus a b)` | The term `(BINARY-+ a b)`. |
| `(library-minus a)` | The term `(UNARY-- a)`. |
| `(library-diff a b)` | The term `(BINARY-+ a (UNARY-- b))`. |
| `(library-lt a b)` | The term `(< a b)`. |
| `(library-le a b)` | The term `(NOT (< b a))`. |
| `(library-positive a)` | The term `(< '0 a)`. |
| `(library-nonnegative a)` | The term `(NOT (< a '0))`. |
| `(library-integer a)` | The term `(INTEGERP a)`. |
| `(library-guards terms)` | The list of the negations of the terms, in order: the side literals of a lemma that holds under those terms. |

## Adding and citing

| Call | Value | Failure |
|---|---|---|
| `(library-library-lemma library name claim step conditions)` | The Library with the lemma `name`, a string, whose clause is `claim` and then the literals of the list `conditions`, and with its entry. `step` is a Step whose literals are among those. | `"assertion"` when the Library has a fact of that name, and when `step` does not prove the clause. |
| `(library-library-definition library name formals body)` | The Library with the definition of the symbol `name`, its fact and its entry. | |
| `(library-library-axiom library name arguments)` | The fact of the symbol `ACL2::name`, with `X`, `Y` and `Z` bound to the terms of the list in order. | `"key"` when there is no such fact. |
| `(library-library-builtin library number term)` | The fact `"built-in-clause-number"` of the ground theory, with `X` bound to `term`. | `"key"`. |
| `(library-library-cite library name arguments evidence)` | The lemma `name`, with `X`, `Y` and `Z` bound to the terms of the list in order, and discharged with the Steps of the list `evidence` in order. | `"key"` when the Library does not have the lemma. `"value"` when a Step of the evidence settles no side literal. |

## Types

`evidence` is a list of Steps that the caller has, `nil` for none.

| Call | Value | Failure |
|---|---|---|
| `(library-library-ints library terms)` | The list of the Steps that assume `(INTEGERP term)` for each term, in order. | |
| `(library-library-type-of library term evidence)` | A Step of `(INTEGERP term)`: the Step of the evidence that proves it; or for an integer constant, a sum, a product, a negation, and a call of `ACL2-COUNT` or `LEN`, a Step from the lemmas `INTEGER-SUM`, `INTEGER-PRODUCT`, `INTEGER-NEGATION`, `COUNT-INTEGER` and `LEN-INTEGER` and the types of the arguments. | `"value"`, with the message `Missing integer premise for` and the text of the term, for any other term. |
| `(library-library-natural library term)` | A Step of `(NATP term)`: for a call of `ACL2-COUNT` or `LEN` and for a sum, from the lemmas `COUNT-NATURAL`, `LEN-NATURAL` and `NATURAL-SUM`; for any other term, by `proof-proof-prove` with the definitions of `NATP` and `NOT`. | That of `proof-proof-prove`. |
| `(library-library-rational library term evidence)` | A Step of `(RATIONALP term)`, from its integer type. | That of `library-library-type-of`. |
| `(library-library-number library term evidence)` | A Step of `(ACL2-NUMBERP term)`, from its integer type. | The same. |
| `(library-type-evidence literal evidence)` | The first Step of the list whose first literal is `literal`, or `nil`. | |
| `(library-type-arguments library terms evidence)` | The list of `library-library-type-of` of each term. | |
| `(library-missing-integer term)` | The failure of `library-library-type-of`. | |

## Sums and comparisons

`integers` is a list of Steps that prove the integer type of the variables that occur, as `library-library-ints` gives.

| Call | Value | Failure |
|---|---|---|
| `(library-library-transport-argument library step equality index)` | The Step with the left side of the equality as argument `index` of its first literal, where the right side stood, tidied. | |
| `(library-library-push-minus n library term evidence)` | An equality of `term` and the same sum with its negations moved inward: the negation of a constant computed, a double negation removed, and the negation of a sum made the sum of the negations. `nil` when nothing moves. `n` is the counter, and the caller passes `1000000`. | `"Fuel"`. |
| `(library-library-linear-form library term evidence)` | An equality of `term` and its normal form as a sum: negations moved inward, the sum nested to the right, constants first and the other terms in the order of their texts with a term before its negation, constants added, a term and its negation removed, and zeros removed. | `"Fuel"`. |
| `(library-library-linear-equal library left right integers)` | A Step of `(EQUAL left right)` for two terms with the same normal form. | `"value"`, with the two normal forms in the message, when they differ. |
| `(library-library-comparison library a b integers)` | The equality of `(< a b)` and `(< '0 (BINARY-+ b (UNARY-- a)))`, by the lemma `LESS-DIFFERENCE`. | |
| `(library-library-less-from-difference library a b positive-difference integers)` | A Step of `(< a b)`, from a Step of `(< '0 d)` in which `d` has the normal form of `b` less `a`. | |
| `(library-library-weak-from-difference library a b nonnegative-difference integers)` | A Step of `(NOT (< b a))`, from a Step of `(NOT (< d '0))` in which `d` has the normal form of `b` less `a`. | |

## The first lemmas

Each of these takes a Library and returns it with definitions and lemmas added, in this order. Every lemma is about `X`, `Y` and `Z`.

| Call | What it adds |
|---|---|
| `(library-library-logic-and-types library)` | `EXCLUDED-MIDDLE`, `IF-FALSE`, `IF-TRUE`; `INTEGER-SUM`, `INTEGER-PRODUCT`, `INTEGER-NEGATION`; `NATURAL-INTEGER`, `NATURAL-NONNEGATIVE`, `NATURAL-FROM-BOUNDS`; `NUMBER-FINITE`, `INTEGER-FINITE`, `NATURAL-ORDINAL`; `FINITE-ORDER`, the equality of `(O< X Y)` and `(< X Y)` for integers; the definition of `SELF-NFIX`, `(IF (NATP X) X '0)`, with `NFIX-NATURAL`, `NFIX-INTEGER` and `NFIX-ORDINAL`; the definition of `SELF-GAP`, `(SELF-NFIX (BINARY-+ X (UNARY-- Y)))`, with `GAP-ORDINAL`. |
| `(library-library-additive-identities library)` | `ADD-ZERO-LEFT`, `ADD-ZERO-RIGHT`, `ADD-SWAP`, `DOUBLE-NEGATION` and `NEGATE-SUM`. It needs the lemmas above. |

## Parts that other books call

In these, `step` is an equality whose right side is being brought to normal form, and `place` is a place in it (`prover/sig/proof.md`), `(1 2)` for the whole right side.

| Call | Value |
|---|---|
| `(library-linear-form-get root place)` | The subterm of `root` that the list of positions `place` leads to. |
| `(library-linear-reassociate n library step place)` | The Step with the sum at `place` nested to the right, by the axiom `ASSOCIATIVITY-OF-+`. `n` is the counter. |
| `(library-linear-sort n library step place changed)` | The Step with the terms of the sum from `place` on brought into order, by `ADD-SWAP` and the axiom `COMMUTATIVITY-OF-+`. The caller passes `nil` for `changed`. `n` is the counter. |
| `(library-linear-combine-pair library a b)` | An equality of `(BINARY-+ a b)` and a constant, when `a` and `b` are constants or one is the negation of the other, and `nil` otherwise. |
| `(library-linear-remove-zero library step name term place evidence)` | The Step rewritten at `place` with the lemma `name`, `ADD-ZERO-LEFT` or `ADD-ZERO-RIGHT`, cited for `term`. |
| `(library-additive-identities-inverse-unique a b sum-zero integers library)` | From `sum-zero`, a Step of `(EQUAL (BINARY-+ a b) '0)`, a Step of `(EQUAL b (UNARY-- a))`. |
