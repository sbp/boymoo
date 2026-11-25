# Alist recognizers

A `recognizer` is `(predicate . trailing-arguments)`. To construct its call,
insert the recognized value immediately after `predicate`. `parts` is the
three-element list of constructor, head and tail fact name strings, in that
order. Terms and Steps follow `prover/sig/proof.md`. A `library` is the shared
Library. A `proof` is the H2 proof search object that contains a Library.

| Function | Arguments in order | Result | Failure |
|---|---|---|---|
| `h2-alist-recognizers-accepted` | Recognizer, value term | Call of the recognizer on the value | Failure for an empty recognizer. |
| `h2-alist-recognizers-label` | Recognizer | ASCII name of the recognizer predicate | A failure if the predicate has no name field or the field cannot be decoded as ASCII. |
| `h2-alist-recognizers-alist-fact` | Library, fact name string, recognizer, ordered binding pairs or `nil` | Instantiated fact Step with the bound parameter supplied when present | A failure from fact lookup or instantiation. |
| `h2-alist-recognizers-cons-closed` | Library, constructor fact name string, recognized singleton Step, recognized tail Step, recognizer | Step recognizing the combined cons | A failure from reading the Steps or proving the recognizer call. |

The constants are `*h2-alist-recognizers-alist*`,
`*h2-alist-recognizers-bounded*`, `*h2-alist-recognizers-assoc*`,
`*h2-alist-recognizers-key*`, `*h2-alist-recognizers-bound*`,
`*h2-alist-recognizers-endp*`, `*h2-alist-recognizers-reverse*`,
`*h2-alist-recognizers-revappend*` and `*h2-alist-recognizers-string*`.

The three lemma-building calls also have entry points with `-with-replies`
appended to their names and an extra final `replies` argument. The shorter
entry points start with `nil` replies. When a derivation is needed, a call
returns `(cons request proof)` with the Search at the point of the derive.
`h2-alist-recognizers-request-p` recognizes the request and
`h2-alist-recognizers-request-arguments` gives the nine arguments to
`h2-recipes-recipes-derive` after the Recipes argument, as listed in `prover/h2/sig/recipes.md`.
`h2-alist-recognizers-request-folded` gives the terms to keep folded for this
one derivation. Restore the surrounding folded-call set when the derivation
ends. Append each `(cons step proof)` or failure to the reply list and repeat
the call from its original arguments. The returned Search includes the
configuration of the latest derivation.

`(h2-alist-recognizers-auxiliary search replies name formula definitions
facts repeat seeds cases folded)` establishes an auxiliary lemma whose
unprefixed stem is `name`. The derivation arguments have their usual forms,
and `folded` is a list of terms. The result is `(value search replies)` with
the updated Search and the remaining replies. Its value is the prefixed
lemma name, a derive request, or a failure carried by a reply. A failure from
adding the lemma is the entire result.
