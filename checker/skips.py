"""Writes the proofs that skip every obligation of a book.

Usage: python3 checker/skips.py LIBRARY STATEMENTS > PROOFS

For each statement of STATEMENTS that has obligations (spec/formats.md,
section 6) it writes the entry (skip NAME): NAME is the theorem's name, or
the name of the first function of a define statement in which some body
calls a function of the statement outside the executable half of an mbe,
or of a constrain statement with at least one formula.  A line that
repeats, byte for byte, an earlier line of LIBRARY or of STATEMENTS takes
no entry.  It reads the files with checks/reader.py.  This is a tool for
the tests and no part of the checker.
"""

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "checks"))
import reader  # noqa: E402

QUOTE = ("sym", b"COMMON-LISP", b"QUOTE")
NIL = ("sym", b"COMMON-LISP", b"NIL")
RETURN_LAST = ("sym", b"ACL2", b"RETURN-LAST")
MBE1_RAW = [QUOTE, ("sym", b"ACL2", b"MBE1-RAW")]


def calls(term, fns):
    """The term calls one of FNS, at any depth outside a constant and
    outside the executable half of an mbe, (return-last 'mbe1-raw a b)."""
    if not isinstance(term, list) or not term or term[0] == QUOTE:
        return False
    if isinstance(term[0], list):          # a lambda application
        return calls(term[0][2], fns) or any(calls(a, fns) for a in term[1:])
    if term[0] == RETURN_LAST and len(term) == 4 and term[1] == MBE1_RAW:
        return calls(term[3], fns)
    return term[0] in fns or any(calls(a, fns) for a in term[1:])


def lines(path):
    with open(path, "rb") as f:
        text = f.read()
    return text.split(b"\n")[:-1] if text else []


def main():
    seen = set(lines(sys.argv[1]))
    out = sys.stdout.buffer
    for line in lines(sys.argv[2]):
        if line in seen:
            continue
        seen.add(line)
        word, data = reader.Reader(line).line()
        name = None
        if word == b"theorem":
            name = data[0]
        elif word == b"define":
            defs = data[1:]
            if any(calls(d[2], [e[0] for e in defs]) for d in defs):
                name = defs[0][0]
        elif word == b"constrain":
            if data[1] != NIL:
                name = data[0][0][0]
        if name is not None:
            out.write(b"(skip " + reader.write(name) + b")\n")


main()
