# Syntax lists

The syntax list tactics use the Library in BookLogic. Their ordered
requests carry the Library at the point where a proof or constant
computation is needed. For example, the equality clause processor
can compute a cons of quoted terms before applying a shape test.

An operation that changes the Library before a failure can return
`(cons failure library)`. The reply protocol is in
`prover/t4/sig/syntax-lists.md`.
