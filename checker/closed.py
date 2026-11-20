"""Confirms that the checker calls only what ACL2 Core allows it.

Usage: python3 checker/closed.py GROUND STATEMENTS

GROUND is spec/ground.txt and STATEMENTS the exported statements of the
checker.  Every function called in a body of a define line of STATEMENTS,
at any depth outside a constant, must be one of the primitives of GROUND,
one of the functions that GROUND defines, or one that STATEMENTS defines.
It prints one line, "closed: N functions defined, each calling only
primitives, ground functions and functions defined", or the names of the
functions called that are none of these; the exit status is 0 only in the
first case.  It reads the files with checks/reader.py.
"""

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "checks"))
import reader  # noqa: E402

QUOTE = ("sym", b"COMMON-LISP", b"QUOTE")


def called(term, out):
    if not isinstance(term, list) or not term or term[0] == QUOTE:
        return
    if isinstance(term[0], list):          # a lambda application
        called(term[0][2], out)
    else:
        out.add(term[0])
    for a in term[1:]:
        called(a, out)


def lines(path):
    with open(path, "rb") as f:
        return f.read().split(b"\n")[:-1]


allowed, defined, calls = set(), set(), set()
for line in lines(sys.argv[1]):
    word, data = reader.Reader(line).line()
    if word == b"primitive":
        allowed.add(data[0])
    elif word == b"define":
        allowed.add(data[1][0])
for line in lines(sys.argv[2]):
    word, data = reader.Reader(line).line()
    if word == b"define":
        for d in data[1:]:
            defined.add(d[0])
            called(d[2], calls)
bad = sorted(reader.write(f).decode() for f in calls - allowed - defined)
if bad:
    print("not closed: " + " ".join(bad))
    sys.exit(1)
print("closed: %d functions defined, each calling only primitives, "
      "ground functions and functions defined" % len(defined))
