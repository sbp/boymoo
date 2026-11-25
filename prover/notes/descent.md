# Measures that decrease

The signatures are in `prover/sig/descent.md`.

## What a recipe is given

An obligation of termination is a clause: the negations of the tests that rule a recursive call, and the goal `(O< smaller measure)` (`prover/sig/termination.md`). A recipe proves the goal and asks for what it needs among the tests. Each test it uses is assumed (`proof-proof-assume`), so the Step it returns has the negations of those tests as side literals, and these are literals of the obligation.

A Hypotheses answers from the tests it holds. A test signed `t` that is a conjunction is taken apart only when one of its conjuncts is asked for, and every conjunct met on the way is kept among the Steps found, so a later question for one of them costs nothing more.

## Two ways to run a recipe

A caller whose hypotheses know more than the tests, as the Rulers of `prover/rulers.lisp` do, runs the same recipe through `descent-query-recipe`. The recipe then stops at the first term that the Hypotheses do not give and returns a request. The caller answers, adds the answer to the replies, and runs the recipe again from the start with the same arguments; the replies given so far are found in the table and the recipe goes further. Nothing but the replies is kept from one run to the next, so the functions stay without memory (`prover/CONVENTIONS.md`). An answer of `nil` is an answer: the recipe goes on without the term, or fails as it would have.

## Lemmas that a recipe adds

With a Library of the kind `:slice` or `:book` the types of `NFIX`, `MIN` and `LENGTH` are proved here, and the first need adds a lemma: `LIBRARY-NFIX`, `MINIMUM-NATURAL` or `LENGTH-NATURAL`. A Step that cites such a lemma is of use only with the Library that has it. So:

- `descent-library-natural` and `descent-library-type-of` return the Library with the Step;
- `descent-measure-ordinal` and `descent-shift` return the Step alone, and `descent-measure-ordinal-with-library` and `descent-shift-with-library` are for the caller that keeps the Library;
- the gap, walk and run recipes return Hypotheses that hold the new Library, when the Hypotheses they were given held the Library that was passed as `lib`. A caller whose Hypotheses hold another object gets the Step and not the lemmas.

A lemma is added once: each function looks for the fact before it proves it.

## The measures

| Recipe | Measure of the caller | What the call does |
|---|---|---|
| Selector | `(ACL2-COUNT x)` | Passes `CAR`s and `CDR`s of `x`, one of them under a test `(CONSP ...)`. |
| Gap | `(SELF-GAP bound i)` | Passes `i + 1` under `i < bound`, or ten times `i` under a bound on `i`. |
| Walk | `(ACL2-COUNT x)`, or one more | Two functions that call each other, of which one may pass `x` itself to the other. The one that does has the measure with one added. |
| Run | A sum of two terms, one of them `(LEN x)` | Passes `(CDR x)` under `(CONSP x)` and leaves the other term. |

`descent-direct-builtin` needs no measure of these forms: it looks for one of the 23 built-in clauses of the ground theory that has the goal as its first literal.

A chain of several selectors is compared by `<` on integers and brought to `O<` at the end by `FINITE-ORDER`. It needs `(CONSP ...)` for one of the selectors only: the others are weak steps, by `COUNT-CAR-WEAK` and `COUNT-CDR-WEAK`, and `library-library-compare-chain` joins weak and strict.
