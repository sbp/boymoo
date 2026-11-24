# Evaluator witnesses

The witness constructor abstracts the argument selectors used by each
primitive operation. It constructs definitions for term evaluation
and list evaluation, then proves the requested constraints. A failed
proof can carry the Evaluator or Library reached before the failure.
