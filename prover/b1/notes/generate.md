# Statement generation

The generator reads statement and aid lines, admits context entries, and
writes a certificate for each obligation it can discharge. The
certificate cache is keyed by the raw statement and retains the context
and auxiliary entries needed for reuse.

`b1-generate-proof-names` scans proof text for uppercase ACL2 symbols
beginning with `SELF-` or `B1-`. It keeps nonoverlapping matches in
discovery order and includes matches in quoted data and strings.

`b1-generate-obligation-output` emits a skip line for an unproved
obligation or an exhausted search budget. A recipe that returns a pair
of a failure and its Library lets the generator retain the auxiliary
entries added by that recipe.
