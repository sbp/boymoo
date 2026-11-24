# Book statements and proof fragments

The batch call `t3-books-book-proofs` takes parsed statement and aid
records. Its proof cache retains fragments in discovery order. The
first fragment whose facts and package state are available supplies the
proof text. A fragment keeps the needed facts and packages in their
first-use order in that text.

The failure cache includes the statement, measure, and digest of the
admitted book lines that precede it. The digest is the sixteen-digit
SipHash-2-4 value of the raw lines in admission order, including their
line terminators. A duplicate line contributes once.

The theorem index holds the book proof context as its Library field.
Measure and witness recipes can replace the context's Library with
`t3-book-theorems-with-library` and keep the package declarations.
