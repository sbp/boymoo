# Constraint witness search

`h2-witnesses-prepare` computes the witness name digest and orders the
candidate lists. `h2-witnesses-prove-prepared` reuses that plan while
processing the ordered replies for call collection, configuration,
and solving. The witness names also identify the entries to remove
if a candidate assignment fails.
