# Reduction and induction

A Reducer carries its proof evidence, allowed definitions, remaining
budget and completed reductions. A rewrite request carries the
library and the term to rewrite. Returning the replies in order
gives the reducer the same evidence when it resumes.

A TreeInduction records the substitutions used to prove smaller
instances. A caller can replace the library after a branch adds facts
and finish the induction with those same substitutions.
