# Arithmetic term tree proofs

`lib` is the B2 Tactics library. Terms and Steps are as specified in
`prover/sig/proof.md`. Evidence and term lists preserve the supplied order.
The functions can return a failure from proof construction instead of
the stated result.

`*b2-term-trees-type-term*` is the symbol named `TERM-LIST-TO-TYPE-TERM`.
`*b2-term-trees-tree-openers*` and `*b2-term-trees-tree-types*` are sets of
theorem names, ordered by their S-expression text.

| Function | Arguments in order | Result |
|---|---|---|
| `b2-term-trees-tree-opener` | `lib`, formula term | Step proving the opener formula |
| `b2-term-trees-typed-list` | `lib`, list of Steps proving pseudo-terms | Step proving the constructed pseudo-term list |
| `b2-term-trees-application` | `lib`, function term, list of Steps proving arguments are pseudo-terms, evidence | Step proving the application is a pseudo-term |
| `b2-term-trees-argument-types` | `lib`, pseudo-term-list Step, list term | Two-element list of the pseudo-term Step for the head and the pseudo-term-list Step for the tail |
| `b2-term-trees-list-tree-type` | `lib`, formula term | Step proving the tree constructor formula |
| `b2-term-trees-fringe-type` | `lib`, formula term | Step proving the fringe formula |
| `b2-term-trees-prove-tree` | `lib`, theorem name, formula term | Step from the selected term tree recipe |
