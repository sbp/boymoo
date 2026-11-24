# The hash

`prover/siphash.lisp` computes SipHash-2-4 of the character codes of a string, with the key of the sixteen bytes 0 to 15. A tactic that brings a helper with its proof, a lemma or a definition, hashes the helper's text and puts digits of the hash in the helper's name, so that the name depends on the text alone. Of ACL2's functions on bits the book uses only `logxor` and `ash`.

| Function | Arguments and value | Failure |
|---|---|---|
| `(siphash string)` | The hash of the string, a natural number below 2^64. | None. |
| `(siphash-hexdigest string)` | That number as sixteen hexadecimal digits in lower case, the highest first. | None. |

The constants are `*siphash-word*`, the number 2^64, and `*siphash-hex*`, the string of the sixteen digits.

## The steps of the computation

No other book calls these. A word is a natural number below 2^64.

| Function | Arguments and value |
|---|---|
| `(siphash-add x y)` | The sum of two words, modulo 2^64. |
| `(siphash-rotate x bits)` | The word `x` turned left by `bits`, a number from 1 to 63: its upper bits become its lower bits. |
| `(siphash-rounds n v0 v1 v2 v3)` | The list `(v0 v1 v2 v3)` of the four words of the state after `n` rounds. |
| `(siphash-load n chars shift word)` | `word` plus the codes of the first `n` characters of the list `chars`, the first moved left by `shift` bits and each later one by 8 bits more. With `shift` and `word` 0 it is the word of those characters, the first in the lowest byte. |
| `(siphash-words n chars v0 v1 v2 v3)` | Takes `n` words of eight characters each into the state. The value is the list of the characters left and the four words. |
| `(siphash-hex n value chars)` | The lowest `n` hexadecimal digits of `value`, the highest first, before the characters of the list `chars`. |

## Test

`sh prover/test/siphash/run.sh`, from the root and after `sh prover/build.sh`, gives nine strings to `siphash-hexdigest` on a runner and compares the values with those written in the script. Two of them are the published values of SipHash-2-4 with this key: `726fdb47dd0e0e31` for the empty string and `a129ca6149be45e5` for the fifteen bytes 0 to 14. On 2026-11-23 it printed `siphash: 9 of 9 strings give the expected value`.
