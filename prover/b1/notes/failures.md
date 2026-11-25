# B1 failures

The generic failure is `(:failure "failure" "")`. Callers recognize it
with `failure-p`. The proving interface returns `nil` for an unproved
obligation.

`b1-measures-try-plan` also recognizes `value`, `assertion`, and `key`
from shared proof, library, and descent operations.
