# Slice proof rules

`lemmas-slice-library-build` selects the slice rules and constructs
the auxiliary count, number and conditional lemmas. A book build
retains its rule selection while it constructs these lemmas.

`lemmas-natural-prepare` and `lemmas-natural-finish-length` let the
caller carry the library across separate requests for natural-number
proofs. A component of a sum can contribute an auxiliary lemma before
the next component is examined. The countdown, remainder and
termination tactics use the resulting library for their next attempts.

`lemmas-slice-library-share-proofs` uses structural equality of Steps
to identify a repeated proof. A Step contains its rule, arguments and
clause.
