# Algebra

The arithmetic recipes construct equality and comparison Steps. A
stateful recipe returns `(cons value lib)` so that later proof attempts
can use the resulting Library, including its auxiliary lemmas.

The `-with-replies` operations can request arithmetic initialization,
a fact proof with supplied Evidence, or a constant computation. The reply
table is keyed by the complete request. The argument and reply forms are
in `prover/t4/sig/algebra.md`.
