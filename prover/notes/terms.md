# Term transformations

`terms-replace-calls` changes function heads in applications and
walks lambda bodies. Quoted values are preserved as data.
`terms-selector-edges` follows a chain of `CAR` and `CDR` calls.
It orders the edges from the requested base to the selected term.
