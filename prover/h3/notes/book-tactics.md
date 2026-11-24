# Book tactic selection

The fallback theorem search tries exact or reduced fact matches and
then the recipes for the theorem's name and shape. Its fact index
returns candidates in their insertion order. The fact-matching
interface with `-with-index` returns the index reached by the lookup.

Induction and constraint witness searches supply their case proofs
through the callbacks in [the book tactic signature](../sig/book-tactics.md).
