# Array header, dimension and lookup proofs

`lib` is a Library as specified in `prover/sig/library.md`. Formulas, names and values are prover terms, and proof arguments are Steps, as specified in `prover/sig/proof.md`. Every call can return a failure as its entire result. A pair with a Library as its tail carries the changes to the library's facts and entries. A result with several Steps lists them in the stated order.

| ACL2 call | Result |
|---|---|
| `(b1-arrays-array-checks lib premise)` | List of the normalized conditions for the `ARRAY1P` assertion Step `premise`, in conjunction order. |
| `(b1-arrays-header-exists lib formula)` | Step for the implication from an array assertion to a cons header. |
| `(b1-arrays-assoc-returned-key lib)` | `(cons name lib)` for the symbol naming the `ASSOC-EQUAL` returned-key lemma and the Library containing it. |
| `(b1-arrays-header-key lib formula)` | `(cons step lib)` for the header-key implication and the resulting Library. |
| `(b1-arrays-header-key-from-cons lib header cons)` | `(cons step lib)` for the key equality of the given `header` term, using Step `cons` showing it is a cons, and the resulting Library. |
| `(b1-arrays-initialized-header-key lib premise)` | `(cons step lib)` for the key equality of the header of the array in Step `premise` and the resulting Library. |
| `(b1-arrays-integer-key-not-header lib integral)` | Step proving the index recognized by Step `integral` differs from the header key. |
| `(b1-arrays-integer-read-guard lib integral)` | Equality Step reducing the header-key test for the index recognized by Step `integral`. |
| `(b1-arrays-association-at-front lib term comparison)` | Equality Step reducing the leading association test of `term` using Step `comparison`. |
| `(b1-arrays-header-at-front lib name items comparison)` | Equality Step reducing the header lookup using Step `comparison` for the leading entry of `items`. |
| `(b1-arrays-array-fields-equal lib claim headers)` | Step proving `claim` about array fields using the equality Step `headers`. |
| `(b1-arrays-field-equation lib field name new old headers)` | Equality Step for applying the given field projection to `new` and `old`, using the header equality Step. |
| `(b1-arrays-compress-array-properties lib formula)` | `(cons step lib)` for the compression properties formula and the resulting Library. |
| `(b1-arrays-inserted-header lib name data index value integral)` | Equality Step for the header before and after inserting `value` at `index`, using Step `integral`. |
| `(b1-arrays-inserted-properties lib formula)` | Step for the formula preserving array fields under insertion. |
| `(b1-arrays-inserted-array lib data-type index value evidence)` | Step showing that inserting `value` at `index` preserves the array recognized by Step `data-type`, from the ordered evidence Steps. |
| `(b1-arrays-update-paths lib call template on-inserted on-compressed)` | Step for the `template` with `call` in the result slot, using the two given Steps on the insertion and compression paths. |
| `(b1-arrays-update-is-array lib formula)` | Step for the formula that updating an array preserves its type. |
| `(b1-arrays-update-array-properties lib formula)` | Step for the formula preserving array fields under update. |
| `(b1-arrays-inserted-value lib name data store value fetch read-integer comparison headers)` | Equality Step for reading the array after insertion, using the fetch index type, index comparison, and header equality Steps. |
| `(b1-arrays-read-updated-array lib formula)` | Step for the read-after-update formula for equal or unequal indices. |
| `(b1-arrays-read-updated-array-cases lib formula)` | Step for the read-after-update formula with a conditional result. |
| `(b1-arrays-lookup-header-only lib header key integral)` | Equality Step for an integer association lookup in a list consisting of `header`, using the header key and integer Steps. |
| `(b1-arrays-scan-header-only lib)` | `(cons name lib)` for the symbol naming the header-only scan lemma and the Library containing it. |
| `(b1-arrays-header-only-fields lib premise only)` | `(cons (list key headers) lib)` with the key Step, the header equality Step for `only`, and the resulting Library. |
| `(b1-arrays-reset-contents lib formula)` | `(cons step lib)` for the reset-contents formula and the resulting Library. |
| `(b1-arrays-reset-fields lib premise)` | `(cons (list reset key headers) lib)` with the reset, key and header equality Steps for the array in `premise` and the resulting Library. |
| `(b1-arrays-reset-properties lib formula)` | `(cons step lib)` for the formula preserving array fields under reset and the resulting Library. |
| `(b1-arrays-reset-is-array lib formula)` | `(cons step lib)` for the formula that resetting an array preserves its type and the resulting Library. |
| `(b1-arrays-read-reset-array lib formula)` | `(cons step lib)` for the read-after-reset formula and the resulting Library. |
| `(b1-arrays-array-forward-modular lib formula)` | Step for the forward implication to the modular array conditions. |

The constants are `*b1-arrays-header*`, `*b1-arrays-dimensions*`, `*b1-arrays-maximum*`, `*b1-arrays-assoc*`, `*b1-arrays-assoc-keyword*`, `*b1-arrays-array*`, `*b1-arrays-compress*`, `*b1-arrays-update*`, `*b1-arrays-default*`, `*b1-arrays-read*`, `*b1-arrays-reset*`, `*b1-arrays-alistp*`, `*b1-arrays-bounded*`, `*b1-arrays-scan*`, `*b1-arrays-name*`, `*b1-arrays-l*`, `*b1-arrays-n*`, `*b1-arrays-val*`, `*b1-arrays-i*`, `*b1-arrays-j*`, `*b1-arrays-d*`, `*b1-arrays-header-key*` and `*b1-arrays-projections*`. `*b1-arrays-projections*` is the ordered list of projection names. The others are terms.
