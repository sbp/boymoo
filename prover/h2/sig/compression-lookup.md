# Compression lookup

A `proof` argument is an H2 BookProof. Terms and Steps have the forms in
`prover/sig/proof.md`. Each result described as a pair is
`(cons value updated-proof)`, including when the requested lemma is already
in the proof. A failure is the entire result. Lemma names returned here are
strings.

| ACL2 call | Arguments and result | Failure |
|---|---|---|
| `(h2-compression-lookup-omitted entry default)` | Two terms. Returns the test that the entry is absent or has the default value. | None. |
| `(h2-compression-lookup-specialize-view proof key entry rest index evidence)` | Four terms and a Step proving the entry present. Returns a pair with the lookup equation for the entry adjoined to the rest of the list. | May return a failure. |
| `(h2-compression-lookup-revappend-view proof first second result)` | Two list terms and the result term. Returns a pair with the equation for their reverse append. | May return a failure. |
| `(h2-compression-lookup-skip-status proof index limit index-type limit-type)` | Two bounds and Steps proving them integers. Returns the Step relating the stopping test to the opposite of the strict comparison. | May return a failure. |
| `(h2-compression-lookup-lookup-on-loop proof backwards)` | The Boolean `backwards` is true for the reverse scan. Returns a pair with the auxiliary lemma name for the selected scan order. | May return a failure. |
| `(h2-compression-lookup-array-bounds proof condition dimension-name)` | A Step proving an array recognizer and a term for the name argument of `DIMENSIONS`. Returns the list of Steps proving the alist, integer dimension, and bounded integer alist, in that order. | May return a failure. |
| `(h2-compression-lookup-lookup-above-bound proof key-type bounded outside)` | Steps proving the key integer, the data bounded and the key outside its upper bound. Returns a pair with the Step equating the lookup to quoted NIL. | May return a failure. |
| `(h2-compression-lookup-header-independent-lookup proof)` | Returns a pair with the auxiliary lemma name for looking up an integer key after adjoining the header. | May return a failure. |
| `(h2-compression-lookup-within-array-lookup proof goal natural typed alist within)` | The lookup equality term and Steps proving natural key, integer dimension, alist data, and the upper bound on the key. Returns a pair with the Step for the equality. | May return a failure. |
| `(h2-compression-lookup-compression-lookup-theorem proof theorem formula)` | The theorem name string and the implication term for the lookup equality. Returns a pair with the Step for the formula. The name suffix `WHEN-<` selects the theorem with an explicit upper bound. | May return a failure. |
| `(h2-compression-lookup-aref-integer-view proof)` | Returns a pair with the auxiliary lemma name for reading an array at an integer key. | May return a failure. |
| `(h2-compression-lookup-compressed-aref proof formula)` | The implication term for the read of the compressed array. Returns a pair with the Step for the formula. | May return a failure. |

The `h2-compression-lookup-within-array-lookup-leaf` function takes the branch value term and its
signed tests first, in the order supplied by `proof-proof-by-value-leaves`,
followed by the proof and captured arguments. The loop induction preserves
the first occurrence of each substitution, visiting the skipped case before
the retained case.

`(h2-compression-lookup-within-array-lookup-leaf value choices proof key
name data old-lookup header header-view header-law key-type typed alist
lower within target)` returns the pair containing the Step equating a
lookup of `key` in the branch value to `target`, or a failure.
`header-view` is the opening equation for `header` and `header-law` is
the name from `header-independent-lookup`. The five Steps `key-type`,
`typed`, `alist`, `lower` and `within` prove integrality of the key,
integrality of the dimension, the alist predicate, and the lower and
upper bounds on the key, respectively. The reply-aware operation takes
the same arguments with `proof` supplied separately.

The read-only `skip-status` and `array-bounds` accept a Search or its
Library. The other proof arguments are opaque BookProof values.

`(h2-compression-lookup-call-with-replies proof operation args replies)`
runs a proof-changing recipe. Supply the list of arguments after `proof`
as `args`, and the recipe name without the book prefix as the keyword
`operation`. An unanswered operation gives
`(:h2-compression-lookup-request operation proof args)`.
`h2-compression-lookup-request-p`, `h2-compression-lookup-request-operation`,
`h2-compression-lookup-request-proof`, and
`h2-compression-lookup-request-args` recognize and read the request.
Append a reply `(cons value proof)` and rerun with the original arguments.
The named functions start with an empty reply list. The reply-aware call
returns `Unproved` in the value position to retain the resulting BookProof.

Operations `:library`, `:keep-folded`, `:restore-fixed-calls`, `:derive`,
`:auxiliary`, `:lemma`, and `:search` follow the reply protocol in
`prover/h2/sig/book-recipes.md`. The operation `:set-fuel` takes the integer
budget and returns `nil` with the BookProof carrying that budget.
`:with-library` takes a replacement Library and returns `nil` with that
Library installed in the BookProof.

`(h2-compression-lookup-search-call search recipe args)` handles the
`:search` recipes `:compression-lookup-assoc-returned-key`,
`:compression-lookup-range-decrease`, `:compression-lookup-list-parts`,
`:compression-lookup-lookup-singleton`, and
`:compression-lookup-compression-laws`. Their `args` are those of the
corresponding functions in `book-logic`, `compression`, or
`alist-recognizers`, after the proof argument. The result is a pair with
the value and resulting Search, a search request, or a failure.
