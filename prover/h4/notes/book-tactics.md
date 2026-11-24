# Rule search

Candidate lookup reads the exact rule bucket first. A compound first
argument with a nonempty head also admits the generic bucket. Rule
templates are used only when the fact's name and clause agree with
the current Library.

A lookup scope records the work for one evidence table. The scope
allocator assigns a fresh token when a caller opens another evidence
table, keeping the earlier lookup records available.
