# Logical equations and truth of conses

`proof` is the H2 proof search object. Terms and Steps have their forms
from `prover/sig/proof.md`. An opening is a Step whose first literal is an
equality. An evidence Step selects a branch of its right side.

| ACL2 call | Result |
|---|---|
| `(h2-book-logic-select-body proof opening evidence)` | Step chaining the opening with the selected branch equation. |
| `(h2-book-logic-logical-equation proof term)` | Step unfolding the term and removing lambda and return-last wrappers from its body. |
| `(h2-book-logic-choice-axiom data)` | The admitted choice formula. `data` is `(name bound free body other)`, with lists of symbols for `bound`, `free` and `other` and the NIL symbol for absent `free` or `other`. |
| `(h2-book-logic-cons-implies-truth proof)` | Proof search object with `SELF-H2-CONSP-NONNIL` added. |
| `(h2-book-logic-nonnil-cons proof)` | `(cons name proof)` with the name string `SELF-H2-CONS-NONNIL` and the resulting proof search object. |
| `(h2-book-logic-assoc-returned-key proof)` | `(cons name proof)` with the name string `SELF-H2-ASSOC-RETURNED-KEY` and the resulting proof search object. |
| `(h2-book-logic-nil-test proof)` | Proof search object with `SELF-H2-EQUAL-NIL` added. |
| `(h2-book-logic-true-boolean proof)` | Proof search object with `SELF-H2-TRUE-BOOLEAN` added. |

Each call can return a failure from its proof operations or from reading
its input. In a result carrying both a value and a proof search object,
the value position can hold a failure so callers retain the object.

The proof search object is Search as specified in
`prover/h2/sig/search.md`. For `select-body` and `logical-equation` a
plain Library or Proof also suffices.

## Rule configuration

The following calls are shared by recipes that configure a Search.
`definitions` and `repeat` are whitespace-separated strings of names,
`facts` is an ordered list of rule names, `seeds` is an ordered list of
Steps, and `cases` is an ordered list of test terms. An optional
`variable` is a name string or `nil`.

| ACL2 call | Result |
|---|---|
| `(h2-book-logic-definition-names definitions names)` | String-to-symbol association list obtained by inserting the Library's definition keys in order into the initial map `names`. Here `definitions` is the definition association list from the Proof. May return a failure. |
| `(h2-book-logic-definition-names-latest-first definitions names)` | The same names as an association list with the latest definition first and earlier pairs of a name left behind it, so that `assoc-equal` finds for each name the symbol that the table above holds. Built without a search for each name. May return a failure. |
| `(h2-book-logic-set-rules search definitions facts repeat split-limit)` | Search configured with the named definitions and facts, or a failure. The names come from the Search's Library. |
| `(h2-book-logic-set-rules-with-names search names definitions facts repeat split-limit)` | Search configured in the same way, using the supplied string-to-symbol map `names`. |
| `(h2-book-logic-derive search formula definitions facts variable depth repeat seeds cases split-limit)` | `(cons step search)` after configuring search and proving the formula. A variable selects list induction. |
| `(h2-book-logic-auxiliary search name formula definitions facts variable depth repeat seeds cases split-limit)` | `(cons label search)` with the auxiliary fact name string and the Search containing the lemma. |

`derive` and `auxiliary` can return a failure or Search hook request in
their value position. Their Search retains its unconsumed hook replies.

`(h2-book-logic-with-saved-result search body)` takes a form that returns
`(cons value search)`. With a Search reply transcript, a completed call
records its value and resulting Search in place of its consumed events.
The recorded Search has no replies. Reading the event attaches the
unconsumed transcript to that Search. An inherited request leaves the
events up to that request available for its reply. Explicit reply lists
use the form directly.
