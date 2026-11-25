# H2 library sessions

A session stores the library's prepared BookProof and a context for the
last admitted earlier prefix. The library proof supplies facts,
definitions, primitive and package tables, auxiliary entries, definition
names, and rule indexes. Two balanced trees hold parsed records by
normalized line and reserved names by their written text.

The prepared BookProof keeps recursive calls by function and definition.
When a new definition is admitted, the index records its recursive calls.
The proof uses a stored Step for the ground non-nil fact where the relevant
Proof fields match. The aid cache holds up to four pairs of an aid list
and its parsed measure and hint tables.

