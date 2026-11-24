# Single-statement proofs

`t4-api-init-proof` supplies the ground Proof. `t4-api-admitted-facts`
admits one parsed statement and records its available choice rules.

`t4-api-rename` substitutes complete symbol tokens. Quoted strings retain
their text. Entry assembly recognizes LF, CRLF, and CR line endings.
Auxiliary names incorporate the SipHash-2-4 digest of the entry text with
the names of its auxiliary dependencies.

`prover/t4/sig/api.md` describes library preparation, admission from parsed
fields, and answer serialization from an admitted context.
