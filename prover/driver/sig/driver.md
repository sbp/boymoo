# Driver functions

`library`, `statements`, `aids` and `ground` are strings holding file text.
An obligation number is its one-based line number in `statements`, counting
every line. A rank is a zero-based position in an obligation's tactic order.
Set names are uppercase strings, such as `"T1"` and `"H4"`.

Options are an association list of `(key . value)` pairs. `:sets` supplies
one order for all obligations. An absent or nil `:sets` uses the orders by
statement kind. `:library-order` selects the orders used for isolated library
statements. `:selected`, when present, is a list of obligation numbers to
try. An absent key selects every obligation. `:ranks`, when supplied as a
natural number, limits the number of ranks to try.

| Function | Arguments and result |
|---|---|
| `(driver-open set library)` | Prepares a session for the named set. Here `library` is a list of lines. |
| `(driver-attempt set session statement line earlier aids)` | `statement` is the parsed statement for `line`. `earlier` and `aids` are lists of lines for the attempt. Returns `(cons blocks session2)`. `blocks` is the ordered list of proof blocks, or `nil` for a miss, an invalid answer or a set failure. |
| `(driver-search library statements aids options)` | Returns the proof entries in statement order, including entries without certificates. |
| `(driver-prove library statements aids options)` | Returns the assembled proof text. |
| `(driver-prove-checked ground library statements aids options)` | Returns `(proof-text verdict)`. The verdict is the checker's first line, without a line feed. A library rejection or a rejection that persists with all skips can be returned as the verdict. |
| `(driver-attempts set library statements aids numbers)` | Tries the requested eligible obligations in the order of `numbers`, with one session. Returns a list of `(number . blocks)` pairs, with nil blocks for a miss or a number that has no eligible obligation. |
| `(driver-entries-from-answers library statements answers)` | Returns the proof entries in statement order with the supplied certificates attached. `answers` is an alist of `(number . blocks)` pairs. |
| `(driver-assemble-answers library statements answers)` | Returns the proof text, with a skip for each obligation without an answer. `answers` is an alist of `(number . blocks)` pairs. |
| `(driver-refuse-answers library statements answers verdict)` | Returns the answer alist after removing the certificate selected for the supplied checker verdict. |
| `(driver-plan library statements aids options)` | Returns `(rank number set)` triples in attempt order, assuming every attempt is still pending. A host omits subsequent attempts for an obligation after it gets a certificate. |

The driver propagates failures from building the worklist. The checked
search returns a `fuel` failure if it exhausts its retry count. It returns
the generic failure when it cannot confirm the skip count or report a
checker rejection. `driver-refuse-answers` propagates a failure from
selecting a certificate to remove. See the [failure convention](../../FAILURES.md).
