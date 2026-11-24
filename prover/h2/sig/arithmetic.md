# Integer order and index proofs

`p` is a Library from `prover/sig/library.md`. Terms and Steps use the
forms in `prover/sig/proof.md`.

| ACL2 call | Result | Failure |
|---|---|---|
| `(h2-arithmetic-integer-order p)` | The updated Library, with integer order and non-nil lemmas. | A failure from proof construction. |
| `(h2-arithmetic-index-lemmas p replies)` | The updated Library, with integer order and index lemmas. | A failure from proof construction or derivation. |
| `(h2-arithmetic-maximum-lemmas p replies)` | The updated Library, with integer order, index and maximum lemmas. | A failure from proof construction or derivation. |
| `(h2-arithmetic-index-lemmas-equality-value term evidence holds p)` | A Step proving equality term `term` equal to quoted `T` or quoted `NIL`, according to Boolean `holds`, from Step `evidence`. | A failure from proof construction. |

`*h2-arithmetic-zp*`, `*h2-arithmetic-nfix*` and `*h2-arithmetic-implies*`
are the corresponding `ACL2` symbol terms. `*h2-arithmetic-integer-rules*`
and `*h2-arithmetic-index-rules*` are lists of rule name strings, in declaration order.

`replies` follows the derivation request protocol in `prover/h2/sig/alists.md`.
When a reply is missing, the result is `(cons request p)`. It can be
recognized by applying `h2-alists-request-p` to the result's `car`.
For the index lemmas, the caller can pass the Library from the derivation
of the requested Step and supply that Step and Library as the sole reply.
The Library supplies the preparation lemmas and any completed index
lemmas. The predecessor bound marks the complete group.
