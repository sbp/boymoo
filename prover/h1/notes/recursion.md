# Structural induction

The recursive-instance walk checks argument compatibility at each call.
It visits the logical branches in term order and accounts for
lambda-bound arguments before matching a call.

Selector descent can add the size lemmas to the library when a nested
path needs them. The caller keeps the updated prover so subsequent
induction steps can use the new facts.
