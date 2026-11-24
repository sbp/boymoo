# Pathname measures

A pathname measure plan gives the measure terms for the cancellation,
parent, and merge definitions in that order. The comparison routines
form integer evidence from the lengths occurring in the requested terms
and use it to compare the measure expressions.

`grep -nE 'b2-pathnames-(path-plan|pathcomparison-init|length-terms)' prover/b2/pathnames.lisp` shows the proof operations. The command was run on 2026-11-23.
