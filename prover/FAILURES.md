# Failures

A function of the prover that cannot give its value gives a **failure** in its place:

```
(:failure KIND MESSAGE)
```

`KIND` and `MESSAGE` are strings. `(failure-p x)` of `prover/basics.lisp` recognizes a failure, and no other value of the program is a list that begins with `:failure`. A caller that cannot go on without the value returns the failure at once; a caller that has another way to try takes it.

## The generic failure

```
'(:failure "failure" "")
```

This is what a function returns when there is nothing a caller could do with the reason. Most failures are of this kind: the search simply did not get through here.

## Kinds that are kept

A kind other than `"failure"` is kept only where some caller tests for it and does something else because of it.

| Kind | Meaning | Message |
|---|---|---|
| `"Fuel"` | A recursion with a counter ran out of its count (see below). | The name of the function. |
| `"Unproved"` | The tactic ran to its end and has no proof. | Empty, or the goal's name. |
| `"Unsupported"`, `"UnsupportedApplication"` | The statement is of a form this tactic does not handle. | Empty. |
| A kind of a set's own | Listed in that set's notes, with the function that tests for it. | Empty. |

The shared books (`basics` through `descent`) return these kinds, and a set may test for them by name:

| Kind | Returned when |
|---|---|
| `"key"` | A table has no entry for the key asked for. |
| `"index"` | A position is outside a sequence. |
| `"value"` | An argument has the right form and a value that cannot be used. |
| `"type"` | An argument has a form the operation does not take. |
| `"assertion"` | A condition the function relies on does not hold. |
| `"attribute"` | A field was asked of a datum that has none (one place, in `proof.lisp`). |

Some sets also name `"stop"`, `"recursion"`, `"lookup"`, `"coding"`, `"decoding"`, `"encoding"` and `"translating"` among the kinds after which they try the next tactic. No book returns these kinds.

## Fuel

Every function is in logic mode and ACL2 admits it with at most a declared measure. A recursion that has no such measure takes a first argument `n`, a natural number that every recursive call decreases, and returns `(:failure "Fuel" "NAME")` when it is 0. The caller at the top passes `1000000`.

## What a message may say

Nothing, in nearly every case. A message never describes the objects of a programming language ("object has no attribute", "index out of range"): if a reader needs to know what failed, the kind says it.
