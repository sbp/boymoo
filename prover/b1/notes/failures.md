# B1 failures

The generic failure is `(:failure "failure" "")`. Callers recognize it
with `failure-p`. The proving interface returns `nil` for an unproved
obligation.

| Kind | Meaning and consumers |
|---|---|
| `Fuel` | A recursive computation used its entire counter. The message names the computation. |
| `Unproved` | An attempt ended without a proof. `b1-search-retry-p` and `b1-search-unproved-p` govern retries in search. `b1-measures-try-plan` tries the next measure. `b1-witnesses-unproved-p` and `b1-generate-unproved-p` allow witness selection and statement generation to proceed. |
| `SearchBudgetExhausted` | The case and rewrite budget was spent. `b1-search-unproved-p`, `b1-witnesses-unproved-p`, and `b1-generate-unproved-p` recognize that outcome. |
| `RuleInapplicable` | A proof rule or measure lookup could not supply the evidence required by a termination plan. `b1-measures-try-plan` continues with another candidate. |

`b1-measures-try-plan` also recognizes `value`, `assertion`, and `key`
from shared proof, library, and descent operations.
