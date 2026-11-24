# Bounds on recursive list operations

Libraries, terms, and Steps have the forms in `prover/sig/library.md` and
`prover/sig/proof.md`. Hypothesis contexts follow
`prover/t2/sig/guarded-selectors.md`. An argument `rulers` denotes the
context constructor. Pass `:ruler-facts` for `RulerFacts` or `:hypotheses`
for the base constructor. The constants `*t2-lists-evens*`,
`*t2-lists-odds*` and `*t2-lists-hons-remove*` are the symbols `EVENS`,
`ODDS` and `HONS-REMOVE-ASSOC` in package `ACL2`.

| Function | Arguments and result |
|---|---|
| `(t2-lists-sum-decrease lib goal hypotheses)` | Library, ordinal decrease goal and context. Returns `(cons step hypotheses)` with the resulting context. |
| `(t2-lists-sum-decrease-decrease n child parent lib hypotheses)` | Natural-number fuel, child and parent terms, Library and context. Pass `1000000` initially. Returns `(cons step hypotheses)` with a Step or `nil` and the resulting context. |
| `(t2-lists-size-at-cons lib size term cons)` | Library, size function symbol, term and its `CONSP` evidence Step. Returns the unfolded size equality Step. |
| `(t2-lists-size-of-cons lib size first rest)` | Library, size function symbol and the two arguments of a `CONS` term. Returns its size equality Step. |
| `(t2-lists-replace-smaller lib bound equality)` | Library, size bound Step and equality Step. Returns the bound Step with the smaller side rewritten. |
| `(t2-lists-replace-larger lib bound equality)` | Library, size bound Step and equality Step. Returns the bound Step with the larger side rewritten. |
| `(t2-lists-empty-bound lib size whole equation)` | Library, size function symbol, source term and equality Step to quoted `NIL`. Returns the weak bound Step. |
| `(t2-lists-induction-hypothesis lib formula smaller-argument descent)` | Library, formula, term replacing `X`, and descent Step. Returns the induction hypothesis Step. |
| `(t2-lists-length-cdr-weak lib)` | Library. Returns the Library with the corresponding lemma. |
| `(t2-lists-evens-bound lib rulers)` | Library and constructor designator. Returns the Library with the bound lemma and its dependencies. |
| `(t2-lists-split-decrease lib goal hypotheses rulers)` | Library, ordinal decrease goal, context and constructor designator. Returns `(cons step (cons lib hypotheses))` with the resulting Library and context. |
| `(t2-lists-removal-bound lib rulers)` | Library and constructor designator. Returns the Library with the bound lemma and its dependencies. |
| `(t2-lists-removal-decrease lib goal hypotheses rulers)` | Library, ordinal decrease goal, context and constructor designator. Returns `(cons step (cons lib hypotheses))` with the resulting Library and context. |

Each function can return a failure in place of its result when term access,
proof construction, or a hypothesis query fails. The fuel argument also
allows a `Fuel` failure on exhaustion.
