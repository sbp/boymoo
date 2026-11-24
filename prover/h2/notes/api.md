# Proof entry naming

The interface prepares a BookProof from the supplied library and earlier
lines. The naming pass visits auxiliary entries in dependency order. For
each entry, it substitutes the assigned names of the dependencies and
uses the uppercase SipHash-2-4 digest of that certificate text in the
new name. The final entry receives the same substitutions.

`h2-api-theorem-entries-from-proof` can retry a theorem from a fresh
trial when the specialized tactic lacks a prerequisite. The failure
kinds that select this path are listed in [failures.md](failures.md).
