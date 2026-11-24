# Character and string completions

`lib` is a B2 tactics library. Terms and Steps follow `prover/sig/proof.md`.

The symbol constants are `*b2-completions-char-eq*`,
`*b2-completions-str-eq*`, `*b2-completions-char-fix*`,
`*b2-completions-str-fix*`, `*b2-completions-characterp*`,
`*b2-completions-stringp*`, `*b2-completions-code*`,
`*b2-completions-coerce*`, `*b2-completions-bitp*`,
`*b2-completions-posp*`, `*b2-completions-bfix*`,
`*b2-completions-bit-identity*` and `*b2-completions-mv-cons*`.
`*b2-completions-list*` is the quoted `COMMON-LISP::LIST` term.
`*b2-completions-fixes*` is an alist from relation symbols to
`(kind fix read extras rule)` records, with character equivalence first and
string equivalence second. `extras` lists trailing argument terms and `rule`
is an axiom name string.

`*b2-completions-fixed-equivalence*`, `*b2-completions-observation-congruence*`,
`*b2-completions-maybe-types*` and `*b2-completions-completion-theorems*`
are membership lists of theorem symbols. Their order is declaration order,
with the union listing fixed equivalence, observation congruence, types,
bit identity and multiple-value selection in that order.

| Call | Result | Failure |
|---|---|---|
| `(b2-completions-observation lib relation value)` | `(cons step lib)` with the observation equality Step at `value` for the symbol `relation` and the library containing its supporting lemma. | Unknown relation or unsuccessful proof construction. |
| `(b2-completions-completed-equivalence lib formula)` | A Step for the equivalence in `formula`. | Unknown relation or unsuccessful proof construction. |
| `(b2-completions-completion-theorem lib name formula)` | `(cons step lib)` with a Step for theorem symbol `name` and term `formula` and the resulting library. | Failure from unpacking the formula or constructing the proof. |
