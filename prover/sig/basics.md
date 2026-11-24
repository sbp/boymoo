# Text, sequences, tables and failures

`prover/basics.lisp` holds the operations on plain data that every other book uses. A text is an ACL2 string. A sequence is a true list, and where a row says so a string. A table is a list of pairs `(key . value)` in the order in which the keys were first put (`prover/CONVENTIONS.md`). Positions count from 0. The keyword `:none` stands for an argument that is left out. White space is the space and the characters of codes 9 to 13 and 28 to 31.

A failure is `(:failure KIND MESSAGE)` (`prover/FAILURES.md`). The last column names the kind of the failure that a function can return in place of its value.

## Failures

| Function | Arguments and value | Failure |
|---|---|---|
| `(failure-p x)` | True exactly when `x` is a list of three members: `:failure`, a string and a string. | None. |

## Text

| Function | Arguments and value | Failure |
|---|---|---|
| `(text-starts-with s prefix)` | Whether the string `s` begins with `prefix`. `prefix` is a string, or a list of strings of which one must fit. | None. |
| `(text-starts-at s prefix start)` | The same from position `start`. A negative `start` counts from the end of `s`, and is taken as 0 when it would fall before the beginning. | None. |
| `(text-ends-with s suffix)` | Whether `s` ends with `suffix`, a string or a list of strings of which one must fit. | None. |
| `(text-join sep strings)` | The strings of the list in order, with the string `sep` between each two. The empty string for an empty list. | None. |
| `(text-upper s)` | `s` with its letters `a` to `z` in upper case. Every other character stays. | None. |
| `(text-lower s)` | `s` with its letters `A` to `Z` in lower case. Every other character stays. | None. |
| `(decimal-text n)` | The decimal digits of the integer `n`, after `-` when it is negative. | None. |
| `(text-find s substring)` | The position of the first occurrence of `substring` in `s`, or `-1`. | None. |
| `(text-split s sep)` | `(text-split-max s sep -1)`. | `"value"` when `sep` is the empty string. |
| `(text-split-max s sep maxsplit)` | The pieces of `s` between the occurrences of the string `sep`, taken from the left, in order. When `maxsplit` is not negative, at most that many splits are made and the last piece holds the rest. With `:none` for `sep`, the pieces are the runs of characters between runs of white space, none of them empty, and the rest after the last split begins at its first character that is not white space. | `"value"` when `sep` is the empty string. |
| `(text-lines s)` | The lines of `s` without their ends. A line ends at a character of code 10 to 13 or 28 to 30, and a return (13) with a line feed (10) after it is one end. A text that ends with a line end has no empty line after it. | None. |
| `(text-strip s chars)` | `s` without the characters of the string `chars` at its two ends, or without white space for `:none`. | None. |
| `(text-strip-left s chars)` | The same at the left end only. | None. |
| `(text-strip-right s chars)` | The same at the right end only. | None. |
| `(text-replace s old new)` | `s` with each occurrence of the string `old`, taken from the left without overlap, replaced by the string `new`. When `old` is empty, `new` is put before every character and at the end. | None. |
| `(text-quoted s)` | `s` written between two quote marks: `'`, or `"` when `s` has a `'` and no `"`. The mark and `\` get a `\` before them. Tab, line feed and return are written `\t`, `\n` and `\r`, and any other character outside the codes 32 to 126 as `\x` and two hexadecimal digits in lower case. | None. |

## Sequences

| Function | Arguments and value | Failure |
|---|---|---|
| `(seq-slice xs start stop)` | The part of the list or string `xs` from position `start` up to `stop`, which is left out. A bound that is not an integer, such as `:none`, is the beginning or the end. A negative bound counts from the end. A bound outside `xs` is brought to its nearer end, and the part is empty when `stop` is not after `start`. | None. |
| `(seq-sorted xs)` | The members of the list in increasing order of `value-less`. | None. |
| `(value-less x y)` | Whether `x` comes before `y`: two rationals by `<`, two strings by `string<`, and two lists by the first members in which they differ, a list coming before every longer list that begins with it. False for any other two values. | None. |
| `(seq-zip xs ys)` | The list of the two-member lists `(x y)` of the members of `xs` and `ys` at the same positions, as far as the shorter goes. | None. |
| `(seq-numbered xs start)` | The list of `(number member)` for the members of `xs` in order, the numbers beginning at the integer `start`. | None. |
| `(seq-range start stop step)` | The integers `start`, `start + step`, and so on, that come before `stop` in the direction of `step`. | `"value"` when `step` is 0. |
| `(seq-index xs x)` | The position of the first member of `xs` equal to `x`. | `"value"` when there is none. The message is the text of `x` and ` is not in list`. |
| `(seq-index-from xs x index)` | The same position counted from `index` for the first member, or `-1` when there is none. | None. |

## Tables

| Function | Arguments and value | Failure |
|---|---|---|
| `(table-get d key default)` | The value of `key` in the table `d`, or `default` when the key is not there. | None. |
| `(table-put d key value)` | `d` with `value` for `key`: in the place of the old value when the key is there, and at the end otherwise. | None. |
| `(table-delete d key)` | `d` without the entry of `key`. | `"key"` when the key is not there. The message is the text of the key. |
| `(table-without d key)` | `d` without the entry of `key`, and with all its entries when the key is not there. | None. |
| `(table-keys d)` | The keys in order. | None. |
| `(table-values d)` | The values in order. | None. |
| `(table-items d)` | The two-member lists `(key value)` in order. | None. |
| `(table-update d other)` | `d` after `table-put` of each entry of the table `other`, in order. | None. |

## The text of a value in a message

