# Book proof worlds

The book prover holds the Library and inference rules, the available
function names, the exact theorem and schema indexes, and the evaluator
equations. Declaration installers extend the world in declaration order.

A certificate collects the entries an obligation needs and the clauses of
its external facts. The worklist can reuse a certificate when those
clauses are available verbatim. A skipped obligation retains the prover
returned by its attempt and produces a skip entry.
