# Reciprocal integrality

`lib` is the Library from `prover/sig/library.md`. Proof arguments and proof
results are Steps from `prover/sig/proof.md`. A result paired with a Library
uses `(cons value lib)`. The Library retains entries and facts in insertion
order. Any failure replaces the entire result.

| Call | Arguments after `lib` | Result | Failure |
|---|---|---|---|
| `(b1-reciprocal-reverse-inequality lib negative)` | Proof of `(not (equal left right))` | Proof of `(not (equal right left))` | Can return a failure |
| `(b1-reciprocal-above-one lib formula)` | Implication about the reciprocal of a term greater than one | Pair of the formula's proof and the resulting Library | Can return a failure |
| `(b1-reciprocal-below-minus-one lib formula)` | Implication about the reciprocal of a term less than minus one | Pair of the formula's proof and the resulting Library | Can return a failure |
| `(b1-reciprocal-integer-reciprocal lib formula)` | Implication about the integrality of the reciprocal of an integer | Pair of the formula's proof and the resulting Library | Can return a failure |
