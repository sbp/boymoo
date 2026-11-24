# Ordered record updates

A Library, a Step and a prover term have the forms in `prover/sig/library.md`
and `prover/sig/proof.md`. Arguments named `evidence`, `facts` or `openers`
are ordered lists. The first two contain Steps and the third contains
terms to unfold. A `label` is the lemma's name string without `B2-`.

Each function that takes a Library can return a failure. When the result is
specified as a pair, it is `(cons result lib)`, with the Library as it
stands at that point. The result field can hold a failure. A completed
`b2-record-update-encoding-lemmas` call returns `nil` in the result field.

| ACL2 call | Arguments and result |
|---|---|
| `(b2-record-update-key record)` | The key projection term of the record term. |
| `(b2-record-update-value record)` | The value projection term of the record term. |
| `(b2-record-update-insert a v tail)` | Key, value and tail terms. Returns the term for the record with that entry prepended. |
| `(b2-record-update-fields lib record typed cons)` | Record term and Steps for its type and cons shape. Returns the list of Steps for nonemptiness, tail type, head cons shape, head value and tail order, in that order. |
| `(b2-record-update-order-or-empty limit record)` | The term asserting that the record is empty or its head key is strictly above the limit term. |
| `(b2-record-update-head-order lib limit record evidence)` | Limit and record terms and the evidence Steps. Returns the Step for strict head order. |
| `(b2-record-update-smaller lib a b different reverse)` | Key terms and Steps for distinctness and failure of the reverse comparison. Returns the Step for `a << b` or the comparison direction given by the trichotomy instance for `b` and `a`. |
| `(b2-record-update-ordered-after lib start first second before after)` | Three successive key terms and two strict order Steps. Returns the Step for the strict comparison from `start` to `second`. |
| `(b2-record-update-with-record lib record typed)` | Record term and type Step. Returns a pair containing a callback request or the completed shape-case Step. |
| `(b2-record-update-encoding-lemmas lib)` | Pair with the Library containing the encoding, decoding and inverse lemmas. |
| `(b2-record-update-prepend-type lib a v tail evidence)` | Key, value and tail terms and evidence Steps. Returns a pair containing a callback request or the Step for the type of the resulting record. |
| `(b2-record-update-set-bound lib)` | Pair containing the lemma symbol for the output head bound and the Library containing the lemma. |
| `(b2-record-update-update-preserves-type lib)` | Pair containing the lemma symbol for preservation of record type and the Library containing the lemma. |
| `(b2-record-update-key-cases lib a record facts)` | Key and record terms and evidence Steps. Returns a pair containing a callback request or the Step from the ordered key cases. |
| `(b2-record-update-lookup-below lib a record typed bound)` | Key and record terms, a type Step and a lower bound Step. Returns the Step that the lookup is nil. |
| `(b2-record-update-record-induction lib label condition target openers on-empty-p extra)` | Condition and target terms, openers, a Boolean indicating whether the empty branch uses a callback, and an ordered list of extra two-element substitution bindings. Returns a pair containing a callback request or the lemma symbol. |
| `(b2-record-update-lookup-after-update lib)` | Pair containing the lemma symbol for lookup of the updated key and the Library containing the lemma. |
| `(b2-record-update-restore-from-lookup lib)` | Pair containing the lemma symbol for setting a key to its existing value and the Library containing the lemma. |
| `(b2-record-update-lookup-other-key lib)` | Pair containing the lemma symbol for lookup of a distinct key and the Library containing the lemma. |
| `(b2-record-update-get-set lib formula typed record same-key)` | Formula term, record type Step, record term and Boolean for lookup of the updated key. Returns a pair containing the proof Step for the formula. |
| `(b2-record-update-record-law lib name formula)` | The law's symbol and formula term. Returns a pair containing the proof Step for the formula. |

A callback request is `(:call branch args continuation)`. Call the
corresponding callback with the positional arguments in `args`. To
continue, pass the Library after that call, the opaque continuation,
and the callback result to the corresponding `-resume` function.
A failure in the callback result completes the call with that failure.

| ACL2 call | Callback branches and arguments |
|---|---|
| `(b2-record-update-with-record-resume lib continuation answer)` | `:empty` and `:nonempty` each take the branch's evidence list and return a Step. |
| `(b2-record-update-prepend-type-resume lib continuation answer)` | `:order` takes the Step that the tail is nonempty and returns a list of additional order Steps. |
| `(b2-record-update-key-cases-resume lib continuation answer)` | `:before`, `:match` and `:after` each take the branch's evidence list and return a Step. |
| `(b2-record-update-record-induction-resume lib continuation answer)` | `:advance` takes the branch's evidence list and the induction hypothesis Step. `:empty` takes the branch's evidence list. Both return a Step. |

The term constants with prefix `*b2-record-update-` and suffix `*` are
`rcdp`, `invalid`, `encode`, `decode`, `get-aux`, `set-aux`, `a`, `b`,
`e`, `r`, `v` and `z`. `*b2-record-update-record-laws*` lists the law
symbols in symbol-name order.

In `smaller`, `different` proves `(NOT (EQUAL a b))` and `reverse`
proves `(NOT (<< a b))`. The returned Step proves `(<< b a)`.

The following interfaces also support the record extensionality recipes.

| ACL2 call | Arguments and result |
|---|---|
| `(b2-record-update-first step)` | The first literal of the Step, or a failure if it is absent. |
| `(b2-record-update-evidence-at known term)` | The Step at `term` in the evidence table made by `b2-tactics-tactics-evidence`, or a failure when the step is missing. |
| `(b2-record-update-request-p value)` | Whether `value` is a callback request. |
| `(b2-record-update-case-request lib test evidence replies)` | Test term, evidence Steps, and an ordered list of supplied `(cons step lib)` replies. Returns a pair containing a signed-case request or the completed Step or failure. A signed-case request uses the Boolean sign in the branch field and the branch evidence as its only callback argument. |
| `(b2-record-update-case-resume lib continuation answer)` | Resumes the signed case with the supplied Step or failure and the Library as it stands after the callback. |
| `(b2-record-update-choose lib test evidence callback captures...)` | Abbreviation for proving the signed cases. Calls the named function with the sign, the one-element list of branch evidence arguments, the Library, and the supplied captures. The named function returns a Step or a failure. |
