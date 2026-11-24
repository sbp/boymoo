# Integer powers

`*b1-powers-fix*` is the symbol `FIX`. `*b1-powers-expt-unfold*` is the
ordered list of `EXPT`, `ZIP`, `=`, and `FIX`, as prover symbols.
The `EXPT` symbol itself is `*b1-quotient-expt*`.

`lib` is the Library from `prover/sig/library.md`. Proof arguments and proof
results are Steps from `prover/sig/proof.md`. A result paired with a Library
uses `(cons value lib)`. The Library retains entries and facts in insertion
order. Any failure replaces the entire result.

| Call | Arguments | Result | Failure |
|---|---|---|---|
| `(b1-powers-expt base exponent)` | Base and exponent terms | The `EXPT` application term | None |
| `(b1-powers-expt-number lib base exponent)` | Library, base and exponent terms | Pair of the numerical type proof and the resulting Library | Can return a failure |
| `(b1-powers-expt-zero lib base)` | Library and base term | Equality reducing `EXPT` with exponent zero | Can return a failure |
| `(b1-powers-multiply-inverse lib a b term inverse numeric)` | Library, terms `a`, `b`, and `term`, a proof of `a*b = 1`, and a proof that `term` is a number | Equality of `a*(b*term)` and `term` | Can return a failure |
| `(b1-powers-build-recurrences lib)` | Library | Library containing the step-up and step-down lemmas | Can return a failure |
| `(b1-powers-natural-predecessor lib natural nonzero)` | Library, proof of naturalness of `n`, and proof that `n` differs from zero | List of the proof that the predecessor is natural and the proof that its count is smaller, in that order | Can return a failure |
| `(b1-powers-power-addition-case lib direction)` | Library and quoted direction term, normally `*proof-one*` or `*proof-neg-one*` | Pair of the lemma name and the resulting Library. `*proof-one*` selects the positive lemma. | Can return a failure |
| `(b1-powers-signed-power-addition lib base i j integer-i integer-j number nonzero)` | Library, base and exponent terms `i` and `j`, proofs of their integrality, and proofs that the base is numeric and nonzero | Pair of the addition equality Step and the resulting Library | Can return a failure |
| `(b1-powers-nonzero-fixed-base lib base nonzero-fix)` | Library, base term, and proof that its `FIX` differs from zero | List of the proofs that the base is numeric and that it is nonzero, in that order | Can return a failure |
| `(b1-powers-exponents-add-two lib formula)` | Library and exponent-addition implication | Pair of the formula's proof and the resulting Library | Can return a failure |
| `(b1-powers-exponent-addition-goal lib formula same-sign)` | Library, exponent-addition implication, and signed integer flag for the shared sign of the exponents. Pass `0` when the sign is unspecified. | Pair of the formula's proof and the resulting Library | Can return a failure |
