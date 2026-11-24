# Rulers

A Rulers object has the form `(:rulers hypotheses)`, with a Hypotheses object as specified in `prover/sig/descent.md`. The constants are `*rulers-atom*`, `*rulers-endp*` and `*rulers-test-definitions*`. Terms and Steps have the forms in `prover/sig/proof.md`.

| Function | Arguments in order | Result | Failure |
|---|---|---|---|
| `rulers-rulers-init` | Library or Proof, list of signed tests, list of extra Steps | Rulers with those tests and extra evidence | A failure from reading a Step |
| `rulers-rulers-proof` | Rulers | Library or Proof | None |
| `rulers-rulers-tests` | Rulers | List of signed tests | None |
| `rulers-rulers-extra` | Rulers | Association list of terms and extra Steps in order | None |
| `rulers-rulers-found` | Rulers | Association list of terms and established Steps in order | None |
| `rulers-rulers-derived` | Rulers | Association list from literals to Steps, in order of first derivation | A failure from proof construction |
| `rulers-rulers-expand` | Natural-number fuel, Rulers, test term, boolean `holds`, evidence Step | List of Steps in derivation order. Pass `1000000` as initial fuel. | A failure from proof construction, or `Fuel` |
| `rulers-rulers-find` | Rulers, term | `(cons step rulers)` with the Step or `nil` and the resulting Rulers | A failure from proof construction |
| `rulers-rulers-require` | Rulers, term | `(cons step rulers)` with the Step and the resulting Rulers | A failure when evidence is missing or proof construction stops |
| `rulers-rulers-cons-ancestor` | Rulers, base term | A `CONSP` Step or `nil` | A failure from proof construction |
| `rulers-rulers-parent-cons` | Rulers, selector application, child evidence Step, boolean `child-is-cons` | A `CONSP` Step for the selector argument | A failure from proof construction |
| `rulers-rulers-positive-lengths` | Rulers | List of equality Steps with `LEN` on the left and a positive integer on the right | A failure from proof construction |
| `rulers-rulers-cons-from-length-test` | Rulers, term | A `CONSP` Step for the term or `nil` | A failure from proof construction |
| `rulers-rulers-positive-length-cons` | Rulers, equality Step for a positive length | A `CONSP` Step for the argument to `LEN` | A failure from proof construction |
| `rulers-rulers-tail-length` | Rulers, equality Step for a positive length | An equality Step for the length of the tail | A failure from proof construction |

When a descent recipe uses a Rulers argument, call `rulers-direct-builtin`, `rulers-selector-chain`, `rulers-selector-decrease`, `rulers-gap-decrease`, `rulers-walk-decrease` or `rulers-run-decrease`. Each has the arguments of the corresponding `descent-` function with Rulers in place of Hypotheses. Each returns the same Step or `nil` paired with the resulting Rulers, or returns a failure. These functions resolve hypothesis queries in the order of the recipe.

| Additional function | Arguments in order | Result | Failure |
|---|---|---|---|
| `rulers-rulers-with-proof` | Rulers, Library or Proof | Rulers with the new proof and the same tests, extra evidence and established evidence | None |
| `rulers-rulers-expand-first` | Natural-number fuel, Rulers, test term, boolean `holds`, evidence Step, requested literal. Pass `1000000` as initial fuel. | First expansion Step whose first literal is the requested literal, or `nil` | A failure encountered before finding a match, or `Fuel` |
