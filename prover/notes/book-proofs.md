# Book proof certificates

`book-proofs-obligation-name` recognizes a recursive group as soon as
it finds a recursive call and uses the first definition's name. A certificate lists the proof entry, the
auxiliary entries it needs and the external facts those entries cite.
The entries retain their source order.

An unproved obligation produces a skip certificate with its failure
kind. Rollback removes the auxiliary entries from that attempt and
retains the earlier library.
