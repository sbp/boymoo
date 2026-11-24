# Permutation laws

The constants `*t3-book-permutations-theorem*`, `*t3-book-permutations-perm*`,
`*t3-book-permutations-member*`, `*t3-book-permutations-remove*`,
`*t3-book-permutations-a*` and `*t3-book-permutations-b*` are prover symbols.
The theorem constant names `PERM-IS-AN-EQUIVALENCE`.

`tactic` is a Permutations object with the form
`(:t3-permutations lib cons atom head tail after-y after-z)`. Its `lib` is a
Library and `cons` and `atom` are the assumption Steps for the two branches
of `(CONSP X)`. `head` and `tail` are the `CAR` and `CDR` calls on `X`.
`after-y` and `after-z` are the removal calls for `head` on `Y` and `Z`.
Use the constructor `t3-book-permutations-permutations-init` and accessors
with the prefix `t3-book-permutations-permutations-` and the field names
shown above. The accessors never return a failure. Terms and Steps use the
forms in `prover/sig/proof.md`.

Every call below can return a failure instead of its stated result. A binding
list `pairs` contains the two-element lists `(variable term)` in the order
supplied by the recipe. `results` and `evidence` are ordered lists of Steps.

| Call | Arguments and result |
| --- | --- |
| `(t3-book-permutations-conjunction lib first second)` | Library and two Steps. Returns the Step proving their conjunction. |
| `(t3-book-permutations-consequence lib contradiction goal)` | Library, contradiction Step and goal term. Returns the Step with the goal added to the clause. |
| `(t3-book-permutations-reverse-denial lib denial)` | Library and Step denying an equality. Returns the Step denying the reversed equality. |
| `(t3-book-permutations-equivalence lib name formula)` | Library, theorem name symbol and formula term. Returns `(cons entry lib)` with the theorem entry and the Library containing its auxiliary lemmas. |
| `(t3-book-permutations-permutations-init lib)` | Library. Returns a Permutations object with the two branch assumptions and the selector and removal terms. |
| `(t3-book-permutations-permutations-lemma tactic name proof)` | Permutations object, unprefixed name string, and Step. Returns `(cons proof tactic)` with the supplied Step and the object containing the added lemma. |
| `(t3-book-permutations-permutations-cite tactic name bindings)` | Permutations object, unprefixed name string and binding list. Returns the instantiated permutation lemma Step. |
| `(t3-book-permutations-permutations-hypothesis tactic formula pairs)` | Permutations object, formula term and bindings. Returns the induction hypothesis Step for the tail of `X`. |
| `(t3-book-permutations-permutations-induct tactic formula pairs step base)` | Permutations object, formula term, bindings, induction Step and base Step. Returns the conclusion Step. |
| `(t3-book-permutations-permutations-open-perm tactic call cons)` | Permutations object, permutation call term and branch Step. Returns the opened equation Step. |
| `(t3-book-permutations-permutations-perm-parts tactic proof cons)` | Permutations object, permutation Step and branch Step. Returns the two-element list of membership and tail Steps for a cons branch, or the Step for the atom branch. |
| `(t3-book-permutations-permutations-perm-from-tail tactic call cons present tail results)` | Permutations object, permutation call term, branch Step, membership Step, tail Step and replacement Steps. Returns the permutation Step. |
| `(t3-book-permutations-permutations-different-member tactic)` | Permutations object. Returns the object containing the different-key membership lemma. |
| `(t3-book-permutations-permutations-other-member tactic a b sequence different)` | Permutations object, two key terms, sequence term and key inequality Step. Returns the membership preservation Step. |
| `(t3-book-permutations-permutations-commute-removal tactic)` | Permutations object. Returns the object containing the removal commutation lemma. |
| `(t3-book-permutations-permutations-perm-cons tactic)` | Permutations object. Returns the object containing the cons permutation lemma. |
| `(t3-book-permutations-permutations-reflexive tactic)` | Permutations object. Returns the reflexivity Step. |
| `(t3-book-permutations-permutations-boolean tactic)` | Permutations object. Returns the Boolean result Step. |
| `(t3-book-permutations-permutations-symmetry tactic)` | Permutations object. Returns `(cons proof tactic)` with the symmetry Step and the object containing its lemma. |
| `(t3-book-permutations-permutations-preserves-member tactic)` | Permutations object. Returns the object containing the membership preservation lemma. |
| `(t3-book-permutations-permutations-preserves-removal tactic)` | Permutations object. Returns the object containing the removal preservation lemma. |
| `(t3-book-permutations-permutations-transitive tactic)` | Permutations object. Returns the transitivity Step. |

`(t3-book-permutations-permutations-with-lib tactic lib)` returns the
Permutations object with the supplied Library and the original assumptions
and terms.
