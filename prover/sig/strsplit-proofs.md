# String split proofs

A library has the form in `prover/sig/library.md`. Terms and proof steps have
the forms in `prover/sig/proof.md`. A function with a library argument can
return a failure in place of its result.

| Function | Arguments in order | Result |
|---|---|---|
| `strsplit-proofs-part` | Index term, input term (the default input is the symbol `*library-x*`) | Projection term |
| `strsplit-proofs-smaller-tail` | Library, input cons step | Tail count descent step |
| `strsplit-proofs-restore` | Library, step, equation step, rewrite location | Rewritten and tidied step |
| `strsplit-proofs-split-count` | Library, formula term | Pair of the count theorem step and the library |
| `strsplit-proofs-split-characters` | Library, formula term | The character list projection theorem step |
| `strsplit-proofs-split-characters-on-delimiter` | Boolean, library, cons step, index term, character step, tail step, induction claim step, definition names | A character list branch step |
| `strsplit-proofs-split-bound` | Library, input cons step | Split count descent step |
| `strsplit-proofs-split-many-characters` | Library, formula term | The character list list theorem step |
| `strsplit-proofs-mapped-strings` | Library, formula term | The string list theorem step for a map |
| `strsplit-proofs-split-strings` | Library, formula term | The string list theorem step for a split |
| `strsplit-proofs-split-tactic` | Library, formula term | Pair of the theorem step or `nil` and the library |
