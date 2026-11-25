# Termination and witness tactics

`lib` is the Library used by the T3 proof routines. For a definition and a
Call use the forms in `prover/sig/termination.md`. For terms and Steps use
`prover/sig/proof.md`. An entry is the result of `proof-proof-entry`.
Declarations are `(function arity)` pairs and formulas are `(name term)`
pairs. All lists of declarations, definitions, Calls and formulas are in
source order. A map is an insertion-ordered association list with
`(key . value)` entries. A failure is the entire result.

| Call | Arguments and result | Failure |
|---|---|---|
| `(t3-tactics-replace-functions term mapping)` | `term` with call heads replaced from the name map, including within lambda bodies. | A failure from inspecting a malformed term. |
| `(t3-tactics-witness-names declarations)` | Map from the declared names to their digest-based witness symbols, in first declaration order. | A failure from reading or writing a name. |
| `(t3-tactics-witnesses lib declarations formulas)` | `(cons entry lib)` for the witness entry and Library with the witness definitions. | A failure from inspecting the inputs or constructing or adding a proof. |
| `(t3-tactics-actual-value term)` | `term` with outer execution wrappers removed and outer lambda calls substituted. | A failure from inspecting or substituting a term, or `fuel`. |
| `(t3-tactics-clock-plan definitions calls)` | Measure map in definition order, or `nil` if there is no clock plan. | A failure from inspecting Calls or their actual arguments. |
| `(t3-tactics-numeric-plan definition calls)` | Singleton measure map for the first matching formal, or `nil`. | A failure from inspecting Calls or their actual arguments. |
| `(t3-tactics-gap-endpoints measure)` | `(upper lower)` for a recognized clipped gap, or `nil`. | A failure from inspecting a malformed term. |
| `(t3-tactics-measure-plan-next definitions calls stored phase)` | `(cons plan next-phase)` for the next yield in order, or `nil` at exhaustion. Pass `:start` for the first phase, then the returned phase to resume. | A failure from the work before the next yield. |
| `(t3-tactics-ordinal lib measure)` | Ordinality Step for the measure term. | A failure from constructing a proof. |
| `(t3-tactics-length-descent lib smaller larger evidence)` | Strict comparison Step for two length measure terms, using the signed-test Evidence. | `unsupported` for a transformed list, or a failure from proof construction. |
| `(t3-tactics-list-tail-descent lib smaller larger evidence)` | Strict comparison Step for a list length and its tail length, using the signed-test Evidence. | `unsupported` for a transformed list, or a failure from proof construction. |
| `(t3-tactics-descent lib clause call)` | `(cons (list step method) lib)` with the decrease Step, method string and resulting Library. `call` is `nil` for an ordinality case. | A failure from selecting or executing a proof recipe. |
| `(t3-tactics-termination lib rulers definitions stored)` | `(cons (list entry methods) lib)` from the first successful plan. `rulers` is the ruler-extender argument of `termination-recursive-calls`. | The last recoverable proof failure, `unsupported` if no plan exists, or a failure from constructing a plan or proof. |

`*t3-tactics-exported-nfix*` and `*t3-tactics-abs*` are term symbols.
`*t3-tactics-components*` and `*t3-tactics-divisions*` are the ordered term
symbol lists for the numeric plan tests.

Ordinality returns `(cons step lib)` to retain the ordinal phase lemmas.
Length descent returns `(step lib evidence)` to retain the projection lemmas
and evidence queries. Tail descent returns `(cons step evidence)`.
