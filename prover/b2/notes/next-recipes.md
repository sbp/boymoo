# Theorem fallbacks

The named theorem dispatcher uses the applicable specialized recipe.
For its general fallback, it tries list preservation when a preservation
plan is available, then type propagation, equivalence, search, and list
induction as the failure kinds permit. If type propagation leaves a
Library with auxiliary lemmas, equivalence and search can use it.

`grep -nE 'b2-next-recipes-prove-new-theorem-(named|fallback|type|search)' prover/b2/next-recipes.lisp` shows the proof operations. The command was run on 2026-11-23.
