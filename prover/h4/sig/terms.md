# Structural term proofs

`p` is the Tactics object defined in `tactics.md`. Terms, bindings, and Steps have the forms in `prover/sig/proof.md`. A result written `(cons value p)` carries the updated Tactics object in its cdr. A failure occupies the entire result. The proof functions may propagate failures from their constituent proof calls.

| ACL2 call | Result and failures |
|---|---|
| `(h4-terms-simplify-evidence p premise evidence expand)` | Rewrite the Step `premise` by normalizing its first literal using the ordered evidence Steps and the definition names in `expand`. May return a failure. |
| `(h4-terms-cons-evidence p nonatom)` | A Step proving the cons test from an atom test's negative Step `nonatom`. May return a failure. |
| `(h4-terms-if-false-impossible p goal contradiction)` | A Step with `goal` in front of the side literals of `contradiction`. A first literal other than quoted NIL produces a failure. |
| `(h4-terms-legal-variables p)` | `(cons name p)` for the local lemma about legal variable names. May return a failure. |
| `(h4-terms-induct-on-tail p formula x atom)` | The induction hypothesis for substituting `(CDR x)` for `x` in `formula`, using the Step `atom`. May return a failure. |
| `(h4-terms-list-recognizer p source target implication-for-head)` | A Step transferring the predicate named by `source` to the predicate named by `target`. `implication-for-head` is a fact name or `nil` for the default. May return a failure. |
| `(h4-terms-length-on-true-lists p)` | `(cons name p)` for the local lemma equating LENGTH and LEN on true lists. May return a failure. |
| `(h4-terms-pseudo-list-case p formula term-proof list-proof)` | The induction case Step for a term-list implication. A callback is represented by an alist from `(child known nonatomic)` to the Step or failure it returns. May return a failure. |
| `(h4-terms-term-implies-pseudo p formula)` | `(cons step p)` for the term-to-pseudo-term implication, with the auxiliary entries added to `p` in declaration order. May return a failure. |
| `(h4-terms-term-list-implies-pseudo p formula)` | The Step for the term-list-to-pseudo-term-list implication. May return a failure. |

The symbol constants are `*h4-terms-atom*`, `*h4-terms-eq*`, `*h4-terms-eql*`, `*h4-terms-length*`, `*h4-terms-null*`, `*h4-terms-stringp*`, `*h4-terms-legal-name*`, `*h4-terms-legal-variable*`, `*h4-terms-symbol-list*`, `*h4-terms-true-list*`, `*h4-terms-arglist*`, `*h4-terms-arglist1*`, `*h4-terms-termp*`, `*h4-terms-term-list*`, `*h4-terms-pseudo-term*`, and `*h4-terms-pseudo-list*`.

`(h4-terms-tactics-build p)` returns the Tactics object after the inherited Library build, with the H4 implication and conjunction methods selected where present. It can return a failure from building an entry.
