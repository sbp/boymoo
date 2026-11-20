"""Splits the lines (value TERM V) and (no-value TERM) of a file in the
format of spec/formats.md into the inputs and expected outputs of the
runner.  Run from the root of the repository:

    python3 runner/test/split.py FILE OUT

It writes OUT.terms and OUT.expected, one term and its value on each
line, for the lines value, and OUT.none, one term on each line, for the
lines no-value.  It uses the reader of checks/reader.py.
"""

import sys

sys.dont_write_bytecode = True
sys.path.insert(0, "checks")
import reader  # noqa: E402


def main():
    src, out = sys.argv[1], sys.argv[2]
    terms, values, none = [], [], []
    with open(src, "rb") as f:
        for line in f.read().split(b"\n")[:-1]:
            word, args = reader.Reader(line).line()
            if word == b"value":
                terms.append(reader.write(args[0]))
                values.append(reader.write(args[1]))
            elif word == b"no-value":
                none.append(reader.write(args[0]))
    for suffix, lines in ((".terms", terms), (".expected", values), (".none", none)):
        with open(out + suffix, "wb") as f:
            f.write(b"".join(x + b"\n" for x in lines))


main()
