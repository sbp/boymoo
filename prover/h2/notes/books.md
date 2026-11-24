# Book proof state

BookProof carries the Library, Search configuration, book rule index,
and written names for the admitted prefix. Search hooks provide the
state needed to apply book rules, fold calls, and charge the rewriting
budget. The focused tactic uses the same state when it delegates to
other books.

Definition admission records recursive calls. The proof of a recursive
definition tries the measure candidates in order and constructs an
entry once it has Steps for the termination clauses.
