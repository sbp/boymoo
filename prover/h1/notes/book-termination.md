# Termination measures

The measure search visits one candidate at a time. A candidate's
ordinality obligations follow definition order, and its decrease
obligations follow recursive call order. A Rulers value carries the
evidence and search state for one obligation.

The search consults the prover's available symbols before using measures
that require particular functions.
