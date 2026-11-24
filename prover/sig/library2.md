# The lemmas of order, length and size

`prover/library2.lisp` builds the rest of the Library that `prover/library.lisp` begins (`prover/sig/library.md`): the order of the integers, the length of a list, the size `ACL2-COUNT`, and the two measures that decrease. It also has three rules that cite those lemmas. `library` is a Library, and terms and Steps have the forms of `prover/sig/proof.md`. Every function can return a failure in place of its value (`prover/FAILURES.md`).

## Rules of comparison

A strict comparison is a Step of `(< a b)`. A weak comparison is a Step of `(NOT (< b a))`, which says that `a` is at most `b`. These rules prove the integer type of each term by `library-library-type-of` with no evidence, so the terms compared are constants, sums, products, negations and calls of `ACL2-COUNT` and `LEN`.

| Call | Value | Failure |
|---|---|---|
| `(library-library-compare-chain library left right)` | From `left`, a comparison of `a` and `b`, and `right`, a comparison of `b` and `c`, of which at least one is strict, a Step of `(< a c)`. It cites `LESS-TRANSITIVE`, `LESS-THEN-WEAK` or `WEAK-THEN-LESS`. | `"assertion"` when the two middle terms differ. `"key"` when both comparisons are weak. |
| `(library-library-as-weak library strict)` | From a Step of `(< a b)`, a Step of `(NOT (< b a))`, by `LESS-TO-WEAK`. | |
| `(library-library-ordinal-comparison library a b)` | The equality of `(O< a b)` and `(< a b)`, by `FINITE-ORDER`. | |
| `(library-compare-chain-arguments literal strict)` | The list `(a b)` of the two terms compared in a literal, strict when `strict` is `t` and weak when it is `nil`. | `"value"` when the literal does not have that form. |

## Building the Library

Each of these takes a Library and returns it with lemmas added.

| Call | What it adds, in order |
|---|---|
| `(library-library-ordered-arithmetic library)` | `LESS-DIFFERENCE`, `POSITIVE-SUM`, `POSITIVE-PRODUCT`, `POSITIVE-NONNEGATIVE`, `POSITIVE-PLUS-NONNEGATIVE`, `NONNEGATIVE-SUM`, `NATURAL-SUM`, `POSITIVE-ONE-PLUS`, `SUCCESSOR-LARGER`, `LESS-THAN-NEXT`, and `TENFOLD-LARGER` by the next function. |
| `(library-library-tenfold-increase library ix px)` | `TENFOLD-LARGER`. `ix` and `px` are Steps that assume `(INTEGERP X)` and `(< '0 X)`. |
| `(library-library-order-lemmas library)` | `LESS-TO-WEAK`, `WEAK-REFLEXIVE`, `LESS-SHIFT`, `LESS-TRANSITIVE`, `LESS-THEN-WEAK`, `WEAK-THEN-LESS`. |
| `(library-library-length-lemmas library)` | `LEN-NATURAL`, by induction on the size of `X`, `LEN-INTEGER`, `LEN-CDR-LESS`. |
| `(library-library-count-lemmas library)` | `SUM-NUMBER`, `NEGATION-NUMBER`, `ABS-NUMBER`, `LENGTH-NUMBER`, `COUNT-NUMBER`, `COUNT-NATURAL`, `COUNT-INTEGER`. |
| `(library-library-weak-selectors library)` | `COUNT-CAR-WEAK`, `COUNT-CDR-WEAK`. |
| `(library-library-integer-measures library)` | `NFIX-DECREASE`, `GAP-DECREASE`. |
| `(library-library-build-before-count library)` | Those of `library-library-logic-and-types`, `library-library-additive-identities`, `library-library-ordered-arithmetic`, `library-library-order-lemmas` and `library-library-length-lemmas`. |
| `(library-library-build-after-count library)` | Those of `library-library-weak-selectors` and `library-library-integer-measures`. |
| `(library-library-build library)` | The whole: before the count, `library-library-count-lemmas`, after the count. From the Library of the ground theory this gives two definitions and 53 lemmas. |

The build is in three parts so that a set whose Library is of the kind `:slice` or `:book` can add lemmas of its own between them. `(library-library-count-lemmas-for-slice library)` is `library-library-count-lemmas` under the name that such a build calls; the proofs of the count lemmas differ by the kind of the Proof, as below.

## The lemmas

The table gives the clause of each lemma of the whole build: the claim, and after it the side literals, which are the negations of what the lemma needs. Packages are left out, and `+`, `*` and `-` stand for `BINARY-+`, `BINARY-*` and `UNARY--`. A lemma is cited with terms for `X`, `Y` and `Z` and with Steps that settle its side literals (`library-library-cite`).

| Lemma | Claim | Side literals |
|---|---|---|
| `EXCLUDED-MIDDLE` | `(NOT X)` | `X` |
| `IF-FALSE` | `(EQUAL (IF X Y Z) Z)` | `X` |
| `IF-TRUE` | `(EQUAL (IF X Y Z) Y)` | `(NOT X)` |
| `INTEGER-SUM` | `(INTEGERP (+ X Y))` | `(NOT (INTEGERP X))`, `(NOT (INTEGERP Y))` |
| `INTEGER-PRODUCT` | `(INTEGERP (* X Y))` | `(NOT (INTEGERP X))`, `(NOT (INTEGERP Y))` |
| `INTEGER-NEGATION` | `(INTEGERP (- X))` | `(NOT (INTEGERP X))` |
| `NATURAL-INTEGER` | `(INTEGERP X)` | `(NOT (NATP X))` |
| `NATURAL-NONNEGATIVE` | `(NOT (< X '0))` | `(NOT (NATP X))` |
| `NATURAL-FROM-BOUNDS` | `(NATP X)` | `(NOT (INTEGERP X))`, `(< X '0)` |
| `NUMBER-FINITE` | `(O-FINP X)` | `(NOT (ACL2-NUMBERP X))` |
| `INTEGER-FINITE` | `(O-FINP X)` | `(NOT (INTEGERP X))` |
| `NATURAL-ORDINAL` | `(O-P X)` | `(NOT (NATP X))` |
| `FINITE-ORDER` | `(EQUAL (O< X Y) (< X Y))` | `(NOT (INTEGERP X))`, `(NOT (INTEGERP Y))` |
| `NFIX-NATURAL` | `(NATP (SELF-NFIX X))` | |
| `NFIX-INTEGER` | `(INTEGERP (SELF-NFIX X))` | |
| `NFIX-ORDINAL` | `(O-P (SELF-NFIX X))` | |
| `GAP-ORDINAL` | `(O-P (SELF-GAP X Y))` | |
| `ADD-ZERO-LEFT` | `(EQUAL (+ '0 X) X)` | `(NOT (INTEGERP X))` |
| `ADD-ZERO-RIGHT` | `(EQUAL (+ X '0) X)` | `(NOT (INTEGERP X))` |
| `ADD-SWAP` | `(EQUAL (+ X (+ Y Z)) (+ Y (+ X Z)))` | |
| `DOUBLE-NEGATION` | `(EQUAL (- (- X)) X)` | `(NOT (INTEGERP X))` |
| `NEGATE-SUM` | `(EQUAL (- (+ X Y)) (+ (- X) (- Y)))` | `(NOT (INTEGERP X))`, `(NOT (INTEGERP Y))` |
| `LESS-DIFFERENCE` | `(EQUAL (< X Y) (< '0 (+ Y (- X))))` | `(NOT (INTEGERP X))`, `(NOT (INTEGERP Y))` |
| `POSITIVE-SUM` | `(< '0 (+ X Y))` | `(NOT (< '0 X))`, `(NOT (< '0 Y))` |
| `POSITIVE-PRODUCT` | `(< '0 (* X Y))` | `(NOT (RATIONALP X))`, `(NOT (RATIONALP Y))`, `(NOT (< '0 X))`, `(NOT (< '0 Y))` |
| `POSITIVE-NONNEGATIVE` | `(NOT (< X '0))` | `(NOT (INTEGERP X))`, `(NOT (< '0 X))` |
| `POSITIVE-PLUS-NONNEGATIVE` | `(< '0 (+ Y X))` | `(NOT (INTEGERP X))`, `(NOT (INTEGERP Y))`, `(NOT (< '0 Y))`, `(< X '0)` |
| `NONNEGATIVE-SUM` | `(NOT (< (+ Y X) '0))` | `(NOT (INTEGERP X))`, `(NOT (INTEGERP Y))`, `(< X '0)`, `(< Y '0)` |
| `NATURAL-SUM` | `(NATP (+ X Y))` | `(NOT (NATP X))`, `(NOT (NATP Y))` |
| `POSITIVE-ONE-PLUS` | `(< '0 (+ '1 X))` | `(NOT (INTEGERP X))`, `(< X '0)` |
| `SUCCESSOR-LARGER` | `(< X (+ '1 X))` | `(NOT (INTEGERP X))` |
| `LESS-THAN-NEXT` | `(< Y (+ '1 X))` | `(NOT (INTEGERP X))`, `(NOT (INTEGERP Y))`, `(< X Y)` |
| `TENFOLD-LARGER` | `(< X (* '10 X))` | `(NOT (INTEGERP X))`, `(NOT (< '0 X))` |
| `LESS-TO-WEAK` | `(NOT (< Y X))` | `(NOT (INTEGERP X))`, `(NOT (INTEGERP Y))`, `(NOT (< X Y))` |
| `WEAK-REFLEXIVE` | `(NOT (< X X))` | `(NOT (INTEGERP X))` |
| `LESS-SHIFT` | `(< (+ X Z) (+ Y Z))` | `(NOT (INTEGERP X))`, `(NOT (INTEGERP Y))`, `(NOT (INTEGERP Z))`, `(NOT (< X Y))` |
| `LESS-TRANSITIVE` | `(< X Z)` | The three integer literals, `(NOT (< X Y))`, `(NOT (< Y Z))` |
| `LESS-THEN-WEAK` | `(< X Z)` | The three integer literals, `(NOT (< X Y))`, `(< Z Y)` |
| `WEAK-THEN-LESS` | `(< X Z)` | The three integer literals, `(< Y X)`, `(NOT (< Y Z))` |
| `LEN-NATURAL` | `(NATP (LEN X))` | |
| `LEN-INTEGER` | `(INTEGERP (LEN X))` | |
| `LEN-CDR-LESS` | `(< (LEN (CDR X)) (LEN X))` | `(NOT (CONSP X))` |
| `SUM-NUMBER` | `(ACL2-NUMBERP (+ X Y))` | |
| `NEGATION-NUMBER` | `(ACL2-NUMBERP (- X))` | |
| `ABS-NUMBER` | `(ACL2-NUMBERP (INTEGER-ABS X))` | |
| `LENGTH-NUMBER` | `(ACL2-NUMBERP (LENGTH X))` | |
| `COUNT-NUMBER` | `(ACL2-NUMBERP (ACL2-COUNT X))` | |
| `COUNT-NATURAL` | `(NATP (ACL2-COUNT X))` | |
| `COUNT-INTEGER` | `(INTEGERP (ACL2-COUNT X))` | |
| `COUNT-CAR-WEAK` | `(NOT (< (ACL2-COUNT X) (ACL2-COUNT (CAR X))))` | |
| `COUNT-CDR-WEAK` | `(NOT (< (ACL2-COUNT X) (ACL2-COUNT (CDR X))))` | |
| `NFIX-DECREASE` | `(O< (SELF-NFIX X) (SELF-NFIX Y))` | `(NOT (INTEGERP X))`, `(NOT (INTEGERP Y))`, `(NOT (< '0 Y))`, `(NOT (< X Y))` |
| `GAP-DECREASE` | `(O< (SELF-GAP X Z) (SELF-GAP X Y))` | The three integer literals, `(NOT (< Y X))`, `(NOT (< Y Z))` |

The three integer literals are `(NOT (INTEGERP X))`, `(NOT (INTEGERP Y))` and `(NOT (INTEGERP Z))`.

The rows are the head lines of the entries that the whole build gives, in their order, with the two definitions `SELF-NFIX` and `SELF-GAP` of `prover/sig/library.md` left out. On 2026-11-23, after `sh prover/build.sh`, the command

```
echo '(ACL2::LEN (BOYMOO-PROVER::LIBRARY-LIBRARY-ENTRIES (BOYMOO-PROVER::LIBRARY-LIBRARY-BUILD (BOYMOO-PROVER::LIBRARY-LIBRARY-INIT (BOYMOO-PROVER::PROOF-PROOF-INIT)))))' | sh prover/run.sh
```

printed `55`, and the same call without `ACL2::LEN` printed entries whose 53 `lemma` head lines are the 53 rows.

## Parts of the build

| Call | Value |
|---|---|
| `(library-order-lemmas-delta-bound a b strict library integers)` | The list `(step guard)`. For `strict` `t`: a Step of `(< '0 (+ b (- a)))` that assumes `(< a b)`, and the side literal `(NOT (< a b))` of that assumption. For `nil`: a Step of `(NOT (< (+ b (- a)) '0))` that assumes `(NOT (< b a))`, and the side literal `(< b a)`. |
| `(library-order-lemmas-transitivity library name left-strict right-strict integers)` | The Library with the lemma `name`, the claim `(< X Z)` from a comparison of `X` and `Y` and one of `Y` and `Z`, each strict or weak as its flag says. |
| `(library-count-lemmas-numeric leaf tests library integer-abs length)` | A Step of `(ACL2-NUMBERP leaf)` for a leaf of the body of `INTEGER-ABS`, `LENGTH` or `ACL2-COUNT` (`prover/sig/proof2.md`, "Proof by the cases of a value"). `integer-abs` and `length` are the symbols of those two functions, and `tests` is not used. A sum, a negation and a call of one of the two functions are settled by the count lemmas already added, and any other leaf by its integer type. When the kind of the Proof is `:slice` or `:book`, a call of `LEN` is settled by the fact `SELF-LEN-NUMBER` when the Proof has it, and a constant by `proof-proof-prove`. |
| `(library-count-lemmas-numeric-lemma library function name integer-abs length)` | The Library with the lemma `name`, `(ACL2-NUMBERP (function X))`, proved by the cases of the body of `function`. |
| `(library-weak-selectors-lemma library head name number)` | The Library with the lemma `name` for the selector `head`, `CAR` or `CDR`, from the fact `"built-in-clause-number"`. |
