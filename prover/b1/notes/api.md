# B1 certificate interface

The statement reader, context preparation, and certificate construction
are described in `prover/b1/sig/api.md`. The session entry points in
`prover/b1/sig/open.md` share the admission and proof construction routines
with the single-call interface.

The certificate writer follows the dependencies of the discharged
obligation, selects the required auxiliary entries, and assigns private
names from their text in dependency order.
