# Certificate naming

L1 reads ASCII statement lines and removes trailing line feeds before checking whether a line is already admitted. It admits the library and earlier lines in that order. The last measure aid for a given name supplies that measure.

A helper name contains the prefix `ACL2::PROVER-L1-`, a 16-digit uppercase SipHash-2-4 digest, and the helper's index within its entry. The digest uses the entry text with preceding helper aliases installed and the entry's own names represented by numbered placeholders. A closed badge lookup uses its conclusion and the preceding support names that determine its proof as the digest input. A definition and its following measure or local choice form one block for naming.

The namespace scan considers helper names in the library, earlier lines, statement, and aids. It recognizes names outside string literals and escaped symbol parts. A collision with a helper's input name or generated name prevents the certificate from being returned.
