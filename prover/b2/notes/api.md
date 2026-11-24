# Proof entry assembly

The theorem dispatcher first looks for an admitted singleton fact with
the requested formula. It then tries the shape, named theorem, and final
theorem recipes in order. Each attempt starts with its own proof context.

Proof assembly gathers the named dependencies of the successful entry in
declaration order. It gives each supporting declaration a name derived
from its text after dependency renaming. The suffix uses the full SipHash
hexadecimal digest in upper case.

`grep -nE 'b2-api-claim|b2-api-entries-assemble-groups|siphash-hexdigest' prover/b2/api.lisp prover/b2/api-entries.lisp` shows the proof operations. The command was run on 2026-11-23.
