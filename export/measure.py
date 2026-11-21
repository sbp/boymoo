"""Counts and sizes of the files that export/run.sh writes.

Usage, from the root of the repository: python3 export/measure.py BOOK ...

It reads build/export/library.* and build/export/books/BOOK.* for each
BOOK named, and prints a summary: for each statements file, the number of
statements of each kind and the size in bytes of each file; whether the
read-back check confirmed every line; for each book that was not
exported, the cause; and what writing every symbol with its package
costs.  checks/reader.py parses the lines.
"""

import gzip
import os
import re
import sys

sys.path.insert(0, "checks")
import reader  # noqa: E402

KINDS = ["package", "hidden-package", "define", "constrain", "choose",
         "theorem", "axiom", "reserve"]


def size(path):
    return os.path.getsize(path) if os.path.exists(path) else 0


def symbol_costs(path):
    """Of the bytes of a file: those of the package lines; of the other
    lines, the bytes of package names and their "::", and of these the
    bytes of ACL2:: and COMMON-LISP::; and the size of the file compressed
    by gzip."""
    prefix = common = package_lines = 0
    data = open(path, "rb").read()
    for text in data.split(b"\n")[:-1]:
        word, args = reader.Reader(text).line()
        if word in (b"package", b"hidden-package"):
            package_lines += len(text) + 1
            continue
        todo = list(args)
        while todo:
            x = todo.pop()
            if isinstance(x, list):
                todo.extend(x)
            elif isinstance(x, tuple) and x[0] == "dot":
                todo.append(x[1])
            elif isinstance(x, tuple) and x[0] == "sym":
                n = len(reader.part(x[1])) + 2
                prefix += n
                if x[1] in (b"ACL2", b"COMMON-LISP"):
                    common += n
    return prefix, common, package_lines, len(gzip.compress(data, 9))


def counts(path):
    c = dict.fromkeys(KINDS, 0)
    lines = 0
    with open(path, "rb") as f:
        for text in f:
            lines += 1
            m = re.match(rb"\(([a-z-]+)", text)
            if m and m.group(1).decode() in c:
                c[m.group(1).decode()] += 1
    return lines, c


def readback(path):
    """The lines (readback ...) and the number of (mismatch ...) lines."""
    result = {}
    mismatches = 0
    if os.path.exists(path):
        for text in open(path, "rb"):
            m = re.match(rb'\(readback "([a-z]+)" ([0-9]+) ([0-9]+)\)', text)
            if m:
                result[m.group(1).decode()] = (int(m.group(2)), int(m.group(3)))
            if text.startswith(b"(mismatch "):
                mismatches += 1
    return result, mismatches


def cause(log):
    """Why a book was not exported, from the log of its run."""
    if not os.path.exists(log):
        return "not run"
    text = open(log, "rb").read().decode("latin-1")
    if "(exit 124)" in text:
        return "time limit of 30 minutes passed"
    if "Heap exhausted" in text or "exhausted" in text.lower():
        return "out of memory"
    for pattern, what in [
            (r"is uncertified|no certificate|not certified|certificate file",
             "no valid certificate"),
            (r"does not exist", "book not found"),
            (r"ttag", "trust tag refused"),
            (r"ACL2 Error[^\n]*", None)]:
        m = re.search(pattern, text)
        if m:
            return what or " ".join(m.group(0).split())[:120]
    return "unknown"


def describe(prefix, name, out, totals):
    st = prefix + ".statements"
    lines, c = counts(st)
    rb, mismatches = readback(prefix + ".readback")
    s_lines, s_ok = rb.get("statements", (0, 0))
    p_lines, p_ok = rb.get("program", (0, 0))
    confirmed = (bool(rb) and s_lines == lines and s_ok == lines and
                 p_ok == p_lines and mismatches == 0)
    pre, common, pk, gz = symbol_costs(st)
    out.append("%s: %d statements (%s); bytes: statements %d, program %d,"
               " aids %d; read back: statements %d of %d, program %d of %d"
               " confirmed%s"
               % (name, lines,
                  ", ".join("%s %d" % (k, c[k]) for k in KINDS),
                  size(st), size(prefix + ".program"), size(prefix + ".aids"),
                  s_ok, lines, p_ok, p_lines,
                  "" if confirmed else " (NOT CONFIRMED)"))
    for k in KINDS:
        totals[k] = totals.get(k, 0) + c[k]
    for k, v in [("lines", lines), ("bytes", size(st)), ("prefix", pre),
                 ("common", common), ("package-lines", pk), ("gzip", gz),
                 ("program", size(prefix + ".program")),
                 ("aids", size(prefix + ".aids"))]:
        totals[k] = totals.get(k, 0) + v
    return confirmed


def costs(what, t):
    if not t.get("bytes"):
        return "%s: no statements" % what
    b = t["bytes"]
    pk = t["package-lines"]
    rest = b - pk
    return ("%s: %d bytes of statements, compressed by gzip -9 to %d"
            " (%.1f%%).  The package lines are %d bytes (%.1f%%).  Of the"
            " other %d bytes, package names and their \"::\" are %d"
            " (%.1f%%), and ACL2:: and COMMON-LISP:: alone %d (%.1f%%)."
            % (what, b, t["gzip"], 100.0 * t["gzip"] / b,
               pk, 100.0 * pk / b, rest,
               t["prefix"], 100.0 * t["prefix"] / max(rest, 1),
               t["common"], 100.0 * t["common"] / max(rest, 1)))


def word(text):
    m = re.match(rb"\(([a-z-]+)", text)
    return m.group(1).decode() if m else ""


def distinct(paths):
    """The distinct lines of the files, and how many there are of each
    word."""
    seen, c = set(), {}
    for path in paths:
        if os.path.exists(path):
            for text in open(path, "rb"):
                if text not in seen:
                    seen.add(text)
                    c[word(text)] = c.get(word(text), 0) + 1
    return seen, c


def made_names(lines):
    """Of the names in the constrain lines among LINES, those that the
    exporter made (spec/formats.md has no other name for them)."""
    n = 0
    for text in lines:
        if text.startswith(b"(constrain "):
            for name in re.findall(rb"\(\(?[^ ()]+::\|[^|]* (?:definition|choice|"
                                   rb"constraint [0-9]+)(?: [0-9]+)?\| ", text):
                n += 1
    return n


def program_counts(path, statements):
    """The define lines of a library's program text that are not
    statements, after the 37 of the ground theory; the functions they
    define; and the attach lines."""
    stm = set(open(statements, "rb").read().split(b"\n"))
    lines = open(path, "rb").read().split(b"\n")[:-1]
    prog = fns = attach = 0
    for i, text in enumerate(lines):
        if text.startswith(b"(attach "):
            attach += 1
        elif i >= 37 and text not in stm:
            prog += 1
            fns += len(reader.Reader(text).line()[1]) - 1
    return prog, fns, attach


def notes(prefixes):
    """For each kind of note, the number of the files that have one."""
    c = {}
    for prefix in prefixes:
        if os.path.exists(prefix + ".notes"):
            kinds = set(m.group(1).decode() for m in re.finditer(
                rb'^\(note "([^"]*)"', open(prefix + ".notes", "rb").read(),
                re.M))
            for k in kinds:
                c[k] = c.get(k, 0) + 1
    return c


def main(books):
    out = []
    lib = {}
    describe("build/export/library", "library", out, lib)
    for text in open("build/export/library.readback"):
        if text.startswith("(complete "):
            out.append("library read back: " + text.strip())
    out.append("")
    totals, done, failed = {}, [], []
    for name in books:
        prefix = "build/export/books/" + name
        if os.path.exists(prefix + ".statements"):
            done.append((name, describe(prefix, name, out, totals)))
        else:
            failed.append((name, cause(prefix + ".log")))
    out.append("")
    out.append("books: %d chosen, %d exported, %d read back and confirmed,"
               " %d not exported"
               % (len(books), len(done), sum(1 for _, ok in done if ok),
                  len(failed)))
    out.append("statements of the books, each book with those of the books"
               " it includes: %d (%s)"
               % (totals.get("lines", 0),
                  ", ".join("%s %d" % (k, totals.get(k, 0)) for k in KINDS)))
    out.append("bytes of the books: statements %d, program %d, aids %d"
               % (totals.get("bytes", 0), totals.get("program", 0),
                  totals.get("aids", 0)))
    for name, why in failed:
        out.append("not exported: %s: %s" % (name, why))
    for name, ok in done:
        if not ok:
            out.append("not confirmed: %s" % name)
    lines, c = distinct("build/export/books/%s.statements" % b
                        for b, _ in done)
    out.append("distinct statement lines over all the books: %d (%s)"
               % (len(lines), ", ".join("%s %d" % (k, c.get(k, 0))
                                        for k in KINDS)))
    lib_lines = set(open("build/export/library.statements", "rb"))
    out.append("names of formulas of a constraint made by the exporter:"
               " library %d, books %d (distinct lines)"
               % (made_names(lib_lines), made_names(lines)))
    aids, a = distinct("build/export/books/%s.aids" % b for b, _ in done)
    declared = sum(1 for t in aids if t.startswith(b"(measure ")
                   and t.endswith(b'"declared")\n'))
    out.append("distinct lines of the aids over all the books: %s; measures"
               " declared %d, default %d"
               % (", ".join("%s %d" % (k, v) for k, v in sorted(a.items())),
                  declared, a.get("measure", 0) - declared))
    prog, fns, attach = program_counts("build/export/library.program",
                                       "build/export/library.statements")
    out.append("program text of the library: %d definitions of %d functions"
               " in program mode, %d attach lines" % (prog, fns, attach))
    lib_notes = re.findall(r'^\(note "([^"]*)"',
                           open("build/export/library.notes").read(), re.M)
    for k in sorted(set(lib_notes)):
        out.append("notes of the library: %s: %d" % (k, lib_notes.count(k)))
    for k, v in sorted(notes(["build/export/books/" + b
                              for b, _ in done]).items()):
        out.append("notes of the books: %s: in %d book%s"
                   % (k, v, "" if v == 1 else "s"))
    out.append("")
    out.append(costs("library", lib))
    out.append(costs("books", totals))
    print("\n".join(out))


if __name__ == "__main__":
    main(sys.argv[1:])
