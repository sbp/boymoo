"""Writes the calls on which runner/test.sh compares the reference
runner with ACL2.  Run from the root of the repository:

    python3 runner/test/gen.py DIR

It writes three files into DIR, each a list of calls (FN ARG ...) whose
arguments are data, in the syntax that ACL2 reads:

  book.calls   the calls of the functions of runner/test/book.lisp;
  lib.calls    calls of functions of ACL2's library, in logic mode and
               in program mode, on generated arguments;
  arith.calls  calls of the arithmetic primitives on generated integers
               of up to 120 digits, fractions and complex rationals,
               with a few arguments that are not numbers.

The arguments are drawn from a generator with a fixed seed, so that the
files are the same at every run.
"""

import sys
from fractions import Fraction

import random

R = random.Random(20261120)


class Sym:
    def __init__(self, pkg, name):
        self.pkg, self.name = pkg, name


class Char:
    def __init__(self, c):
        self.c = c


class Cx:
    def __init__(self, re, im):
        self.re, self.im = re, im


def lisp(x):
    """The text of X that ACL2 reads."""
    if x is None:
        return "nil"
    if x is True:
        return "t"
    if isinstance(x, int):
        return str(x)
    if isinstance(x, Fraction):
        return str(x.numerator) if x.denominator == 1 else "%d/%d" % (x.numerator, x.denominator)
    if isinstance(x, Cx):
        return "#c(%s %s)" % (lisp(x.re), lisp(x.im))
    if isinstance(x, str):
        return '"' + x.replace("\\", "\\\\").replace('"', '\\"') + '"'
    if isinstance(x, Sym):
        return "%s::%s" % (x.pkg, x.name)
    if isinstance(x, Char):
        return "#\\Space" if x.c == " " else "#\\" + x.c
    if isinstance(x, tuple):          # a dotted list: (items, tail)
        return "(" + " ".join(map(lisp, x[0])) + " . " + lisp(x[1]) + ")"
    if not x:
        return "nil"
    return "(" + " ".join(map(lisp, x)) + ")"


PRINTABLE = [chr(c) for c in range(32, 127)]
STANDARD = [chr(c) for c in range(32, 127)] + ["\n"]
SYMBOLS = [Sym("ACL2", n) for n in ("RT-A", "RT-B", "RT-C", "RT-ZEBRA", "APPLE")] + \
    [Sym("KEYWORD", "K"), Sym("COMMON-LISP", "CAR"), None, True]


def big(digits):
    n = R.randint(1, 10 ** R.randint(1, digits))
    return -n if R.random() < 0.5 else n


def nonzero(digits):
    n = 0
    while n == 0:
        n = big(digits)
    return n


def rational(digits=30):
    k = R.random()
    if k < 0.4:
        return big(digits)
    if k < 0.5:
        return R.choice([0, 1, -1, 2 ** 29, -2 ** 29, 2 ** 29 - 1, -2 ** 29 - 1, 10 ** 9, -10 ** 18])
    return Fraction(big(digits), abs(nonzero(digits)))


def number(digits=30):
    if R.random() < 0.3:
        return Cx(rational(digits), Fraction(nonzero(digits), abs(nonzero(digits))) if R.random() < 0.5
                  else nonzero(digits))
    return rational(digits)


def string(chars=PRINTABLE):
    return "".join(R.choice(chars) for _ in range(R.randint(0, 10)))


def atom():
    k = R.random()
    if k < 0.3:
        return R.randint(-20, 20)
    if k < 0.6:
        return R.choice(SYMBOLS)
    if k < 0.75:
        return string()
    if k < 0.85:
        return Char(R.choice(PRINTABLE))
    return rational(5)


def anything(depth=0):
    if depth < 3 and R.random() < 0.3:
        return [anything(depth + 1) for _ in range(R.randint(0, 4))]
    return atom()


def tlist():
    return [atom() for _ in range(R.randint(0, 8))]


def alist():
    return [([atom()], atom()) for _ in range(R.randint(0, 6))]


def dotted():
    return (tlist() or [1], atom() or 1) if R.random() < 0.5 else tlist()


def nat():
    return R.randint(0, 12)


def quotient_pair():
    j = rational(8) or 3
    return [j * R.randint(-300, 300) + Fraction(R.randint(-5, 5), R.randint(1, 4)), j]


def sym():
    return R.choice(SYMBOLS[:6])


def symlist():
    return [sym() for _ in range(R.randint(0, 6))]


def symalist():
    return [([sym()], atom()) for _ in range(R.randint(0, 6))]


def stdchar():
    return Char(R.choice(PRINTABLE))


def substring():
    s = string()
    a = R.randint(0, len(s))
    return [s, a, R.randint(a, len(s))]


def rats():
    return [R.choice([rational(3), R.randint(-9, 9)]) for _ in range(R.randint(0, 6))]


def car_alist():
    return [([R.randint(-50, 50)], atom()) for _ in range(R.randint(0, 8))]


L, C = "ACL2", "COMMON-LISP"
LIB = [
    (L, "BINARY-APPEND", lambda: [tlist(), tlist()]),
    (C, "REVAPPEND", lambda: [tlist(), tlist()]),
    (C, "REVERSE", lambda: [R.choice([tlist(), string()])]),
    (L, "LEN", lambda: [dotted()]),
    (L, "TRUE-LISTP", lambda: [dotted()]),
    (C, "NTH", lambda: [nat(), tlist()]),
    (C, "NTHCDR", lambda: [nat(), tlist()]),
    (L, "TAKE", lambda: [nat(), tlist()]),
    (C, "LAST", lambda: [dotted()]),
    (C, "BUTLAST", lambda: [tlist(), nat()]),
    (L, "MEMBER-EQUAL", lambda: [atom(), tlist()]),
    (L, "ASSOC-EQUAL", lambda: [atom(), alist()]),
    (L, "REMOVE-EQUAL", lambda: [atom(), tlist()]),
    (L, "REMOVE-DUPLICATES-EQUAL", lambda: [tlist() + tlist()]),
    (L, "UNION-EQUAL", lambda: [tlist(), tlist()]),
    (L, "INTERSECTION-EQUAL", lambda: [tlist(), tlist()]),
    (L, "SET-DIFFERENCE-EQUAL", lambda: [tlist(), tlist()]),
    (L, "ADD-TO-SET-EQUAL", lambda: [atom(), tlist()]),
    (L, "PAIRLIS$", lambda: [tlist(), tlist()]),
    (L, "STRIP-CARS", lambda: [alist()]),
    (L, "STRIP-CDRS", lambda: [alist()]),
    (L, "PUT-ASSOC-EQUAL", lambda: [atom(), atom(), alist()]),
    (L, "SUBSETP-EQUAL", lambda: [tlist(), tlist()]),
    (L, "NO-DUPLICATESP-EQUAL", lambda: [tlist()]),
    (L, "POSITION-EQUAL", lambda: [atom(), R.choice([tlist(), string()])]),
    (L, "MAKE-LIST-AC", lambda: [nat(), atom(), tlist()]),
    (L, "REMOVE1-EQUAL", lambda: [atom(), tlist()]),
    (L, "TRUE-LIST-FIX", lambda: [dotted()]),
    (L, "FIRST-N-AC", lambda: [nat(), tlist(), tlist()]),
    (L, "STRING-LISTP", lambda: [R.choice([tlist(), [string() for _ in range(3)]])]),
    (C, "FLOOR", quotient_pair),
    (C, "CEILING", quotient_pair),
    (C, "TRUNCATE", quotient_pair),
    (C, "ROUND", quotient_pair),
    (C, "MOD", quotient_pair),
    (C, "REM", quotient_pair),
    (C, "EXPT", lambda: [number(4), R.randint(-12, 12)]),
    (C, "ABS", lambda: [rational()]),
    (C, "SIGNUM", lambda: [rational()]),
    (C, "MAX", lambda: [rational(), rational()]),
    (C, "MIN", lambda: [rational(), rational()]),
    (L, "NFIX", lambda: [R.choice([rational(), atom()])]),
    (L, "IFIX", lambda: [R.choice([rational(), atom()])]),
    (L, "RFIX", lambda: [R.choice([number(), atom()])]),
    (L, "ZP", lambda: [R.choice([rational(3), atom()])]),
    (L, "ZIP", lambda: [R.choice([rational(3), atom()])]),
    (C, "EVENP", lambda: [big(20)]),
    (C, "ODDP", lambda: [big(20)]),
    (C, "INTEGER-LENGTH", lambda: [R.randint(-5000, 5000)]),
    (C, "ASH", lambda: [R.randint(-5000, 5000), R.randint(-8, 8)]),
    (L, "BINARY-LOGAND", lambda: [R.randint(-300, 300), R.randint(-300, 300)]),
    (L, "BINARY-LOGIOR", lambda: [R.randint(-300, 300), R.randint(-300, 300)]),
    (C, "LOGNOT", lambda: [big(30)]),
    (C, "CHAR-UPCASE", lambda: [stdchar()]),
    (C, "CHAR-DOWNCASE", lambda: [stdchar()]),
    (C, "UPPER-CASE-P", lambda: [stdchar()]),
    (C, "LOWER-CASE-P", lambda: [stdchar()]),
    (C, "ALPHA-CHAR-P", lambda: [stdchar()]),
    (C, "CHAR<", lambda: [stdchar(), stdchar()]),
    (L, "STRING-APPEND", lambda: [string(), string()]),
    (C, "STRING-UPCASE", lambda: [string()]),
    (C, "STRING-DOWNCASE", lambda: [string()]),
    (C, "SUBSEQ", substring),
    (C, "STRING<", lambda: [string("ab"), string("ab")]),
    (C, "STRING-EQUAL", lambda: [string("aAb"), string("aAb")]),
    (L, "EXPLODE-NONNEGATIVE-INTEGER", lambda: [R.randint(0, 10 ** 6), R.choice([2, 8, 10, 16]), None]),
    (L, "SYMBOL<", lambda: [sym(), sym()]),
    (L, "LEXORDER", lambda: [anything(), anything()]),
    (L, "ALPHORDER", lambda: [atom(), atom()]),
    (L, "MERGE-SORT-LEXORDER", lambda: [tlist() + tlist()]),
    (L, "SYMBOL-LISTP", lambda: [tlist()]),
    (L, "INTEGER-LISTP", lambda: [R.choice([tlist(), rats()])]),
    (L, "RATIONAL-LISTP", lambda: [R.choice([tlist(), rats()])]),
    (L, "CHARACTER-LISTP", lambda: [tlist()]),
    (L, "ALISTP", lambda: [R.choice([alist(), tlist()])]),
    (L, "COUNT-NON-NILS", lambda: [tlist()]),
    (L, "LISTIFY", lambda: [tlist()]),
    (L, "LISTLIS", lambda: [tlist(), tlist()]),
    (L, "INTEGER-ABS", lambda: [big(12)]),
    (L, "FIRST-N-AC-REV", lambda: [nat(), tlist(), tlist()]),
    (L, "MERGE-SORT-CAR-<", lambda: [car_alist()]),
    # ACL2 runs its own functions in program mode as their Common Lisp
    # code even with guard checking :none, where eq compares two strings
    # by their place in memory; so these are called within their guards,
    # on symbols.
    (L, "FIRST-NON-MEMBER-EQ", lambda: [symlist(), symlist()]),
    (L, "FIRST-ASSOC-EQ", lambda: [symlist(), symalist()]),
    (L, "SET-DIFFERENCE-ASSOC-EQ", lambda: [symlist(), symalist()]),
    (L, "SORT-SYMBOL-LISTP", lambda: [[sym() for _ in range(R.randint(0, 6))]]),
    (L, "STRING-PREFIXP", lambda: [string("ab"), string("ab")]),
]

ARITH = [
    ("BINARY-+", 2), ("BINARY-*", 2), ("UNARY--", 1), ("UNARY-/", 1), ("<", 2),
    ("NUMERATOR", 1), ("DENOMINATOR", 1), ("REALPART", 1), ("IMAGPART", 1),
    ("COMPLEX", 2), ("EQUAL", 2), ("INTEGERP", 1), ("RATIONALP", 1),
    ("COMPLEX-RATIONALP", 1), ("ACL2-NUMBERP", 1),
]
ARITH_PKG = {"<": C, "NUMERATOR": C, "DENOMINATOR": C, "REALPART": C, "IMAGPART": C,
             "COMPLEX": C, "EQUAL": C, "INTEGERP": C, "RATIONALP": C}

BOOK = [
    "(rt-three 5)", "(rt-three-user 5)", "(rt-s 3)", "(rt-s-user 3)",
    "(rt-he 1)", "(rt-he (1))", "(rt-il 1)", "(rt-il (1))", "(rt-nx 3)",
    "(rt-ch 3)", "(rt-mbe (1 2))", "(rt-mbe 7)", "(rt-deep 1000)",
    "(rt-loop 100000 0)", "(rt-ev 101)", "(rt-od 101)", "(rt-pm 1)",
    "(hard-error rt \"RT\" nil)",
]


def arith_arg():
    k = R.random()
    if k < 0.05:
        return R.choice([Sym("ACL2", "RT-A"), "s", Char("a"), None, [1, 2]])
    return number(R.choice([3, 9, 20, 60, 120]))


def main():
    d = sys.argv[1]
    with open(d + "/book.calls", "w") as f:
        f.write("".join(c + "\n" for c in BOOK))
    with open(d + "/lib.calls", "w") as f:
        for pkg, name, args in LIB:
            for _ in range(25):
                f.write("(%s::%s %s)\n" % (pkg, name, " ".join(map(lisp, args()))))
    with open(d + "/arith.calls", "w") as f:
        for _ in range(4000):
            name, n = R.choice(ARITH)
            if name == "EQUAL" and R.random() < 0.5:
                a = arith_arg()
                args = [a, a]
            else:
                args = [arith_arg() for _ in range(n)]
            f.write("(%s::%s %s)\n" % (ARITH_PKG.get(name, L), name, " ".join(map(lisp, args))))


main()
