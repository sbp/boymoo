# Constructor proofs

The constructor recipes may request a knowledge query, a proof of a
fact from the library, a proof using specified definitions, or a
recognizer implication. The knowledge and fact queries can share
the same Evidence.

The optional recognizer can request constructor typing from
`t4-list-types-query`. The `-with-library` entry points preserve the
Library across failures and requests. See `prover/t4/sig/constructors.md`.
