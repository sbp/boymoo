# Printing support order

`h4-book-printing-printing-support` returns the facts that the printing
lemmas add to the support library, in the order in which they were added.

The packing proof and the division measure tactic install the returned
facts in that order. The first usable fact determines the name cited by a
proof step, so where two facts serve the same clause, the one added
first is cited.
