# L1 book obligations

A Certificate is `(:l1-certificate source steps reason helpers)`. The source is a byte string or a list of byte strings in entry order. A string in the list ends between entries and keeps a definition with its measure or its local choice. `steps` is the rule count, `reason` is empty for a proof, and `helpers` is the list of required Library entries in Library order. A Library entry has the form `(kind name counts source)` from `prover/sig/library.md`.

`(l1-books-make-certificate source steps reason helpers)` takes the four fields in order. `l1-books-certificate-sources` returns the list of source strings, and `l1-books-certificate-source` joins them. `l1-books-certificate-steps`, `l1-books-certificate-reason`, and `l1-books-certificate-helpers` return their fields directly.

Proofs, Steps, terms, definitions, Calls, and Hypotheses follow the shared signatures under `prover/sig/`. `kind` is the statement word string, `data` is its list of parsed fields, and `raw` is the statement byte string with its line terminator. `calls` is the list of Calls in source order. `measures` is a map from function symbols to measure terms. `stored` maps function symbols to pairs `(measure relation)`. `choices` is the list of choice rules in admission order. `names` maps source function symbols to replacement function symbols. Maps preserve first insertion order unless otherwise stated.

| Call | Result | Failure |
|---|---|---|
| `(l1-books-obligation kind data)` | `(name calls)`, with `nil` for the name if there is no obligation and `nil` for the calls if it is not a recursive definition. | A failure from reading fields or computing calls. |
| `(l1-books-generate proof choices raw kind data name calls stored)` | Certificate for the supplied obligation, or a skip Certificate with the failure reason. | A failure from constructing the certificate. |
| `(l1-books-prove-formula proof formula evidence definitions rewriting)` | Step proving `formula` under the ordered list of evidence Steps. `definitions` is the ordered list of symbols to unfold. Pass `t` for `rewriting` to enable rewriting. | `Unproved` when the permitted tactics do not produce a proof, or a failure from proof construction. |
| `(l1-books-arithmetic-library)` | The Library of arithmetic lemmas in build order. | A failure from building the Library. |
| `(l1-books-selector-case proof goal hypotheses)` | `(cons step hypotheses)` with the Step or `nil` and the resulting original Hypotheses. | A failure from opening the goal, finding evidence, or constructing the Step. |
| `(l1-books-length-sum-case proof goal hypotheses)` | `(cons step hypotheses)` with the Step or `nil` and the resulting original Hypotheses. | A failure from inspecting the goal, finding evidence, or constructing the Step. |
| `(l1-books-lexer-proofs proof)` | LexerProofs built with the current Proof facts and definitions and the arithmetic entries. | A failure from building the Library or the lexer proofs. |
| `(l1-books-length-case proof goal hypotheses lexer)` | `(cons (list step lexer) hypotheses)` with the Step or `nil`, the existing or newly built LexerProofs or `nil`, and the resulting original Hypotheses. | A failure from inspecting the goal, finding evidence, or constructing the Step. |
| `(l1-books-fact-names source)` | Distinct names from `fact` lines in the source byte string, ordered by the ACL2 text of the name data. | A failure from reading the matching lines. |
| `(l1-books-arithmetic-helpers source entries)` | Entries needed directly or through their dependencies, in the order supplied in `entries`. | A failure from reading fact names. |
| `(l1-books-measure-proof proof name definitions calls measures)` | Measure Certificate with any needed helper entries, or `nil` when the measure tactic has no proof. `definitions` is the list of definition triples in statement order. | A failure from reading or assembling the measure certificate. |
| `(l1-books-entry kind name fields steps)` | Certificate from the header fields and the ordered list of conclusion Steps, with empty reason and helpers. | A failure from constructing the proof entry. |
| `(l1-books-replace-calls term names)` | Term with the selected function symbols replaced in call position, including inside lambda bodies. | A failure from reading an empty application or a malformed lambda. |
| `(l1-books-constant-witness proof name data tag)` | Certificate for the first constant witness that succeeds, or `nil`. `data` contains constrained functions and formulas. `tag` is the suffix string for generated names. | A failure from reading or constructing the witness certificate. |
| `(l1-books-fact-dependencies certificate facts)` | Association list of cited names found in `facts`, ordered by the ACL2 text of the name data. | A failure from reading fact names. |
| `(l1-books-with-helpers entries)` | List of `(name certificate)` pairs in input order with each helper's source and count included before its first use. | A failure from malformed entry data. |
| `(l1-books-prepare-book statements aids base base-choices shared expected statement-name)` | List of `(name certificate)` pairs in obligation order. `statements` and `aids` are lists of parsed `(raw kind data)` lines. `base` is the Proof for the library, `base-choices` is its choice list, and `shared` is the set of raw library lines. `expected` is the checker's skip text. The caller may pass `nil` as the statement label. | A failure from preparing the book or a mismatch in the skip text. |

`*l1-books-simple-definitions*` lists the default definitions in the order used by the formula and constant-witness recipes. `prepare_book` takes parsed inputs and a checker result. Its certificate cache is omitted. `run_books` is the file, process, and reporting interface.

`(l1-books-prepare-book-with-cache statements aids base base-choices shared expected statement-name cache)` takes the same parsed inputs and the available certificates. It returns `(cons entries cache)` with the resulting entries and cache, or a failure as in `l1-books-prepare-book`. The cache is an insertion-ordered alist from raw lines to lists of `(certificate dependencies)` pairs in discovery order. Each dependency map is the result of `l1-books-fact-dependencies`. This call retains explicit certificate reuse across books because the supplied certificates can determine the emitted proof. `l1-books-prepare-book` uses an empty initial cache and returns only the entries.

`(l1-books-generate-prepared proof choices raw kind data name calls stored preparation)` has the result and failure behavior of `l1-books-generate`. The first field of `preparation` is the result of `l1-books-arithmetic-library`, or `nil` to build it when a proof needs it.

The second field may be the result of `l1-rewriting-rewriter-prepared` for the same Proof. With `nil`, each rewrite or induction attempt obtains its Rewriter from `l1-rewriting-rewriter-init`.
