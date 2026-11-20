"""A reader for the text of spec/formats.md, and a check that files obey it.

Usage: python3 checks/reader.py FILE ...

Each file is read line by line, every line is written out again from
what was read, and the result must be the file, byte for byte.  One line
is printed for each file: "ok FILE: N lines", or "FAIL FILE: line N".
The exit status is 0 only if every file is read.
"""

import sys

PLAIN = set(b"ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-+*/<=>!?$%&_^~.@")
HEX = b"0123456789ABCDEF"


class Reader:
    def __init__(self, line):
        self.s, self.i = line, 0

    def peek(self):
        return self.s[self.i] if self.i < len(self.s) else -1

    def take(self, text):
        if not self.s.startswith(text, self.i):
            raise ValueError
        self.i += len(text)

    def escaped(self, close):            # the inside of "..." or |...|
        out = bytearray()
        while self.peek() != close:
            c = self.peek()
            if c == 92:                  # backslash and two hex digits
                h = self.s[self.i + 1:self.i + 3]
                if len(h) != 2 or h[0] not in HEX or h[1] not in HEX:
                    raise ValueError
                c = int(h, 16)
                if 32 <= c <= 126 and c != close and c != 92:
                    raise ValueError
                self.i += 3
            elif 32 <= c <= 126:
                self.i += 1
            else:
                raise ValueError
            out.append(c)
        self.i += 1
        return bytes(out)

    def plain(self):
        j = self.i
        while self.peek() in PLAIN:
            self.i += 1
        return self.s[j:self.i]

    def part(self):                      # one part of a symbol
        if self.peek() == 124:
            self.i += 1
            p = self.escaped(124)
            if p and all(c in PLAIN for c in p):
                raise ValueError
            return p
        return self.plain()

    def rational(self, t):
        num, _, den = t.partition(b"/")
        digits = num[1:] if num.startswith(b"-") else num
        for d in (digits, den) if b"/" in t else (digits,):
            if not d.isdigit() or (d[0] == 48 and d != b"0"):
                raise ValueError
        if num == b"-0":
            raise ValueError
        if b"/" in t:
            n, d = int(num), int(den)
            a, b = abs(n), d
            while b:
                a, b = b, a % b
            if d < 2 or a != 1:
                raise ValueError
            return ("ratio", n, d)
        return int(num)

    def datum(self):
        c = self.peek()
        if c == 40:                      # a list
            self.i += 1
            items, tail = [self.datum()], None
            while self.peek() == 32:
                self.i += 1
                if self.s.startswith(b". ", self.i):
                    self.i += 2
                    tail = self.datum()
                    if isinstance(tail, list) or tail == ("sym", b"COMMON-LISP", b"NIL"):
                        raise ValueError
                    break
                items.append(self.datum())
            self.take(b")")
            return items if tail is None else items + [("dot", tail)]
        if c == 34:
            self.i += 1
            return ("str", self.escaped(34))
        if c == 35:
            if self.s.startswith(b"#\\", self.i):
                h = self.s[self.i + 2:self.i + 4]
                if len(h) != 2 or h[0] not in HEX or h[1] not in HEX:
                    raise ValueError
                self.i += 4
                return ("char", int(h, 16))
            self.take(b"#C(")
            re = self.rational(self.plain())
            self.take(b" ")
            im = self.rational(self.plain())
            self.take(b")")
            if im == 0:
                raise ValueError
            return ("complex", re, im)
        j = self.i
        p = self.part()
        if self.s.startswith(b"::", self.i):
            self.i += 2
            return ("sym", p, self.part())
        if c == 124 or self.i == j:
            raise ValueError
        return self.rational(p)

    def line(self):                      # (word datum ...)
        self.take(b"(")
        j = self.i
        while self.peek() in b"abcdefghijklmnopqrstuvwxyz-":
            self.i += 1
        word, args = self.s[j:self.i], []
        if not word:
            raise ValueError
        while self.peek() == 32:
            self.i += 1
            args.append(self.datum())
        self.take(b")")
        if self.i != len(self.s):
            raise ValueError
        return word, args


def escape(b, close):
    return b"".join(bytes([c]) if 32 <= c <= 126 and c not in (close, 92)
                    else b"\\%02X" % c for c in b)


def part(p):
    return p if p and all(c in PLAIN for c in p) else b"|" + escape(p, 124) + b"|"


def rat(x):
    return b"%d" % x if isinstance(x, int) else b"%d/%d" % x[1:]


def write(x):
    if isinstance(x, list):
        if isinstance(x[-1], tuple) and x[-1][0] == "dot":
            return b"(" + b" ".join(map(write, x[:-1])) + b" . " + write(x[-1][1]) + b")"
        return b"(" + b" ".join(map(write, x)) + b")"
    if isinstance(x, int) or x[0] == "ratio":
        return rat(x)
    if x[0] == "str":
        return b'"' + escape(x[1], 34) + b'"'
    if x[0] == "char":
        return b"#\\%02X" % x[1]
    if x[0] == "complex":
        return b"#C(" + rat(x[1]) + b" " + rat(x[2]) + b")"
    return part(x[1]) + b"::" + part(x[2])


def check(name):
    data = open(name, "rb").read()
    lines = data.split(b"\n")
    if lines.pop() != b"":
        return "FAIL %s: the last line does not end" % name
    for n, text in enumerate(lines, 1):
        try:
            word, args = Reader(text).line()
            if b"(" + b" ".join([word] + [write(a) for a in args]) + b")" != text:
                raise ValueError
        except (ValueError, IndexError):
            return "FAIL %s: line %d" % (name, n)
    return "ok %s: %d lines" % (name, len(lines))


if __name__ == "__main__":
    results = [check(name) for name in sys.argv[1:]]
    print("\n".join(results))
    sys.exit(any(r.startswith("FAIL") for r in results))
