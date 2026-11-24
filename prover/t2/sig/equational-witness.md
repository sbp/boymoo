# Equational witnesses

`lib` is a Library as specified in `prover/sig/library.md`. Terms, symbol data, Steps and proof entries use the forms in `prover/sig/proof.md`.

| ACL2 call | Arguments and result | Failure |
|---|---|---|
| `(t2-equational-witness-available term lib)` | Whether the operators in the term are available in `lib`. | None for prover terms. |
| `(t2-equational-witness-defining-equation lib name arity formulas)` | `name` is a witness symbol, `arity` is its argument count and `formulas` is a list of terms in source order. Returns `(parameters body)` for the first usable orientation of the first usable equation, with the written orientation checked first. | `Unproved` when there is no equation, or a failure for malformed formula data. |
| `(t2-equational-witness-witness lib data)` | `data` contains the list of `(name arity)` witness declarations followed by the list of `(name formula)` claims. Returns `(cons entry library)` with the witness entry and the Library extended by the witness definitions. The name map retains first insertion order, with a repeated key taking its new value in place. | `Unproved` for a missing equation or unsuccessful search, or a failure from proof construction or malformed witness data. A failure is the entire result. |
| `(t2-equational-witness-with-prepared-rules lib data prepared)` | The same result as `witness`, using the supplied prepared Rules value after installing the witness definitions. `nil` selects ordinary indexing. | As in `witness`. |
