# Proof interface checks

The interface check supplies an engine with three possible replies. It
checks that the statement and line groups reach the engine with the
`T2` prefix, and that the interface returns the proof or `nil` as specified
in `prover/t2/sig/api.md`.

All three assertions passed on 2026-11-23 with this command.

~~~
sh prover/t2/build.sh --run-acl2 1800 < prover/t2/test/api/wrapper.lsp
~~~
