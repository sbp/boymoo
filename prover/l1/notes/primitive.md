# Primitive application and badges

Primitive recipes use a WarrantProof for the quoted `CAR`, `CDR`, and `SYMBOLP` computations in symbolic evaluation. A badge witness uses `CDR` of a quoted badge row to obtain the badge.

The badge table keeps the serialized rows and their offsets. Lookup certificates cite blocks of rows and preserve their order in the table. The certificate record carries temporary facts while a proof needs them.
