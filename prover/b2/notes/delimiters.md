# Delimiter projections

The `STD::SPLIT-///` recipes induct on the input list and select the
requested result with `MV-NTH`. The post-delimiter proof carries the
input type premise into the induction cases. The delimiter dispatcher
returns the Step paired with the Library containing the projection
lemmas. Their targets are the theorems
`STD::TRUE-LISTP-OF-SPLIT-///.PRE-///` and
`STD::TRUE-LISTP-OF-SPLIT-///.POST-///` of the ACL2 book `xdoc/autolink`,
each after the lines of that book before it and with the full library.

`grep -nE 'b2-delimiters-delimiter-(type|theorem)' prover/b2/delimiters.lisp prover/b2/next-recipes.lisp` shows the proof operations. The command was run on 2026-11-23.
