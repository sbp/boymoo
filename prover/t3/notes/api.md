# Proof requests

The input normalization preserves the order of source lines. The scope
admits each distinct normalized line once and applies proof recipes
triggered by declarations. A theorem index then serves proof requests
for the admitted scope.

Auxiliary name substitution uses the token bounds of the dependency
scan in `logic.lisp`. Each auxiliary entry receives a name after the
names it cites have been substituted. The final proof uses those
substituted names and retains its line terminators.
