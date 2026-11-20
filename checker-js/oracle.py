"""Check primitive values against recorded ACL2 results and Python fractions."""

from fractions import Fraction
from pathlib import Path
import random
import runpy
import subprocess
import sys
import tempfile


CL = b"COMMON-LISP::"
ACL2 = b"ACL2::"
QUOTE = CL + b"QUOTE"
NIL = CL + b"NIL"
T = CL + b"T"


def form(*parts):
    return b"(" + b" ".join(parts) + b")"


def quote(datum):
    return form(QUOTE, datum)


def number(value):
    real, imag = value
    if imag:
        return b"#C(" + str(real).encode("ascii") + b" " + str(imag).encode("ascii") + b")"
    return str(real).encode("ascii")


def acl2_values():
    reader = runpy.run_path("checks/reader.py")
    parse = reader["Reader"]
    write = reader["write"]
    primitives = {
        parse(line).line()[1][0]
        for line in Path("spec/ground.txt").read_bytes().splitlines()
        if line.startswith(b"(primitive ")
    }
    values, refusals, found = [], [], set()
    packages = b""
    for line in Path("checks/expected/facts.txt").read_bytes().splitlines():
        if line.startswith(b'(package "BM-P4" '):
            packages += line + b"\n"
        if line.startswith((b"(value ", b"(no-value ")):
            word, data = parse(line).line()
            call = data[0]
            if isinstance(call, list) and call[0] in primitives:
                found.add(call[0])
                if word == b"value":
                    values.append((write(call), write(data[1])))
                else:
                    refusals.append(write(call))
    if found != primitives or not packages:
        raise RuntimeError("ACL2 data do not cover every primitive and its package prerequisites")
    return values, refusals, packages


def numeric_values():
    rng = random.Random(271828)
    values = []

    def datum(n):
        return str(n).encode("ascii")

    def record(fn, *arguments, result):
        values.append((form(fn, *map(quote, arguments)), result))

    def rational(bits):
        return Fraction(rng.getrandbits(bits) * rng.choice((-1, 1)), rng.getrandbits(bits) + 1)

    for index in range(256):
        bits = (8, 25, 53, 91, 256, 733, 1019, 2048)[index % 8]
        a, b, c, d = [rational(bits) for _ in range(4)]
        if index % 4 == 0:
            a, c = Fraction(a.numerator), Fraction(c.numerator)
        if index % 7 == 0:
            b = Fraction(0)
        if index % 11 == 0:
            c, d = a, -b
        left, right = number((a, b)), number((c, d))
        norm = a * a + b * b
        record(ACL2 + b"BINARY-+", left, right, result=number((a + c, b + d)))
        record(ACL2 + b"BINARY-*", left, right, result=number((a * c - b * d, a * d + b * c)))
        record(ACL2 + b"UNARY--", left, result=number((-a, -b)))
        record(ACL2 + b"UNARY-/", left, result=number((a / norm, -b / norm)) if norm else b"0")
        record(CL + b"<", left, right, result=T if (a, b) < (c, d) else NIL)
        record(CL + b"<", left, number((a, d)), result=T if b < d else NIL)
        record(CL + b"NUMERATOR", datum(a), result=datum(a.numerator))
        record(CL + b"DENOMINATOR", datum(a), result=datum(a.denominator))
        record(CL + b"REALPART", left, result=datum(a))
        record(CL + b"IMAGPART", left, result=datum(b))
        record(CL + b"COMPLEX", datum(c), datum(d), result=right)
        record(CL + b"EQUAL", left, right, result=T if (a, b) == (c, d) else NIL)
        record(CL + b"INTEGERP", datum(a), result=T if a.denominator == 1 else NIL)
        record(ACL2 + b"COMPLEX-RATIONALP", left, result=T if b else NIL)
    return values


def check(engine, directory, packages, values, expected):
    library, statements, proofs = (Path(directory, name) for name in ("library", "statements", "proofs"))
    library.write_bytes(packages)
    with statements.open("wb") as book, proofs.open("wb") as proof:
        for index, (term, value) in enumerate(values):
            name = ACL2 + b"ORACLE-" + str(index).encode("ascii")
            book.write(form(b"theorem", name, form(CL + b"EQUAL", term, quote(value))) + b"\n")
            proof.write(form(b"theorem", name) + b"\n" + form(b"compute", term) + b"\n(qed)\n")
    result = subprocess.check_output(["sh", "checker-js/check.sh", library, statements, proofs, engine])
    if result.splitlines()[0] != expected:
        sys.stderr.buffer.write(result)
        raise SystemExit(1)


def main():
    if len(sys.argv) > 2:
        raise SystemExit("Usage: python3 checker-js/oracle.py [ENGINE]")
    engine = sys.argv[1] if len(sys.argv) == 2 else "node"
    acl2, refusals, packages = acl2_values()
    numeric = numeric_values()
    Path("build").mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="checker-js-oracle-", dir="build") as directory:
        check(engine, directory, packages, acl2, b"accepted")
        for term in refusals:
            check(engine, directory, packages, [(term, NIL)], b"rejected proofs 2")
        check(engine, directory, b"", numeric, b"accepted")
    print("all oracle tests passed (%d ACL2 values, %d ACL2 refusals, %d numeric values)" %
          (len(acl2), len(refusals), len(numeric)))


if __name__ == "__main__":
    main()
