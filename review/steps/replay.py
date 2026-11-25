"""Generate and certify the books of steps from the repository root."""

import os
from collections import Counter
from pathlib import Path
import re
import shutil
import subprocess
import sys
from time import perf_counter

from book import Book, RULES, clear_caches, lisp_string, native_symbol, read_trace, write_lisp


BUILD = Path("build/steps")
TOOLS = BUILD / "tools"
EMPTY = BUILD / "empty"
VERSION = '(ld "checks/version.lsp")'
QUIET = "(set-inhibit-output-lst '(warning warning! observation prove proof-tree event))"
STRICT = ":uncertified-okp nil :defaxioms-okp nil :skip-proofs-okp nil :ttags nil"
STEP = re.compile(rb"^\((" + b"|".join(rule.encode("ascii") for rule in RULES) + rb") ")
PROOF_INPUTS = ("proofs", "library-proofs")


def acl2(forms, log, timeout=120):
    commands = list(forms) + ["(good-bye)"]
    source = ("\n".join(commands) + "\n").encode("latin-1")
    with log.open("wb") as stream:
        try:
            result = subprocess.run(["acl2"], input=source, stdout=stream,
                                    stderr=subprocess.STDOUT, timeout=timeout)
        except subprocess.TimeoutExpired:
            print(f"ACL2 timed out. See {log}.", file=sys.stderr)
            return False
    return result.returncode == 0


def certify(stem, portcullis, *, axioms=False):
    stem.with_suffix(".cert").unlink(missing_ok=True)
    lsp = stem.with_suffix(".lsp")
    write_lisp(lsp, [*portcullis, '(value-triple (cw "~%STEPS PORTCULLIS OK~%"))'])
    flag = "t" if axioms else "nil"
    book = lisp_string(str(stem.with_suffix(".lisp")))
    commands = [VERSION, QUIET, f'(ld "{lsp}" :ld-error-action :error)',
                f'(certify-book "{stem}" ? nil'
                f" :defaxioms-okp {flag} :skip-proofs-okp nil :ttags nil :pcert nil)",
                f"""(mv-let (erp pair state)
                     (cert-annotations-and-checksum-from-cert-file {book} state)
                     (if (and (not erp)
                              (equal (assoc-eq :skipped-proofsp (car pair)) '(:skipped-proofsp))
                              (equal (assoc-eq :ttags (car pair)) '(:ttags))
                              (iff (cdr (assoc-eq :axiomsp (car pair))) {flag}))
                         (value (cw "~%STEPS CERTIFICATE OK~%"))
                       (er soft 'steps "The certificate annotations were unexpected.")))"""]
    log = stem.with_suffix(".log")
    ran = acl2(commands, log)
    output = log.read_bytes()
    confirmed = (ran and stem.with_suffix(".cert").is_file()
                 and b"\nSTEPS PORTCULLIS OK\n" in output
                 and b"\nSTEPS CERTIFICATE OK\n" in output)
    if not confirmed:
        stem.with_suffix(".cert").unlink(missing_ok=True)
    return confirmed


def build_tools():
    TOOLS.mkdir(parents=True, exist_ok=True)
    EMPTY.write_bytes(b"")
    names = "base read terms rules admit check".split()
    shutil.copyfile("checker/package.lsp", TOOLS / "package.lsp")
    for name in names + ["canon"]:
        source = Path("checks" if name == "canon" else "checker") / (name + ".lisp")
        shutil.copyfile(source, TOOLS / source.name)
        # The package declaration is the checker's only portcullis command.
        portcullis = [] if name == "canon" else ['(ld "package.lsp" :ld-error-action :error)']
        if not certify(TOOLS / name, portcullis):
            raise RuntimeError(f"ACL2 could not certify {source}. See {TOOLS / (name + '.log')}.")


class Case:
    def __init__(self, name, inputs, expected=None):
        self.name = name
        self.inputs = inputs
        self.expected = expected
        self.out = BUILD / name
        self.trace = self.out / "trace.txt"

    @classmethod
    def specimen(cls, directory, expected):
        paths = [directory / (name + ".txt") for name in ("library", "statements", *PROOF_INPUTS)]
        return cls(str(directory), [p if p.is_file() else EMPTY for p in paths], expected)


def specimens():
    yield Case.specimen(Path("spec/example"), "accepted")
    for root in (Path("checker/cases"), Path("checker-js/cases")):
        for verdict in sorted(root.glob("*/verdict.txt")):
            expected = verdict.read_bytes().splitlines()[0].decode("ascii")
            if expected == "accepted" or expected.startswith("provisional "):
                case = Case.specimen(verdict.parent, expected)
                for path in case.inputs[2:]:
                    with path.open("rb") as proofs:
                        if any(STEP.match(line) for line in proofs):
                            yield case
                            break


def self_input():
    library = Path("build/checker/library.statements")
    statements = Path("build/checker/checker.statements")
    proofs = Path("build/self/checker.proofs")
    library_proofs = Path("build/self/library/checker.proofs")
    if not all(path.is_file() and path.stat().st_size
               for path in (library, statements, proofs, library_proofs)):
        log = BUILD / "self-build.log"
        with log.open("wb") as stream:
            result = subprocess.run(["sh", "review/self/run.sh"], stdout=stream,
                                    stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(f"Could not build the checker's source proof. See {log}.")
    return Case("self", [library, statements, proofs, library_proofs], "accepted")


def collect(cases, log):
    commands = [
        VERSION, QUIET,
        f'(include-book "{TOOLS / "check"}" {STRICT})',
        f'(include-book "{TOOLS / "canon"}" {STRICT})',
        '(ld "checker/acl2-run.lsp" :ld-error-action :error)',
        '(ld "review/steps/trace.lsp" :ld-error-action :error)',
    ]
    for case in cases:
        case.out.mkdir(parents=True, exist_ok=True)
        case.trace.unlink(missing_ok=True)
        args = [lisp_string(str(path)) for path in [*case.inputs, case.trace]]
        commands.append(f"(steps-trace {' '.join(args)} state)")
    if not acl2(commands, log, timeout=300):
        raise RuntimeError(f"ACL2 could not collect the traces. See {log}.")


def js_verdict(case):
    result = subprocess.run(["sh", "checker-js/check.sh", *(str(p) for p in case.inputs), "node"],
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120)
    lines = result.stdout.splitlines()
    if result.returncode or not lines:
        raise RuntimeError("The JavaScript checker failed to produce a verdict.")
    return lines[0].decode("ascii")


def certify_case(case, book, packages):
    if book.hidden:
        if not certify(case.out / "symbols", book.package_events(hidden_open=True)):
            return "package declarations", case.out / "symbols.log"
        if not certify(case.out / "hidden", ()):
            return "hidden packages", case.out / "hidden.log"
        packages = [f'(include-book "hidden" {STRICT})'] + packages
    if not certify(case.out / "book", packages, axioms=book.axioms):
        return "ACL2 refused the book", case.out / "book.log"
    return None


def package_refusal(message):
    if b"DEFPKG " in message and b"disallows lower case characters" in message:
        return "ACL2 rejected a package name with a lower-case character"
    if b"DEFPKG " in message and b"raw Lisp" in message:
        return "ACL2 rejected a package name reserved by the host Lisp"
    return None


def statement_refusal(book, message):
    markers = list(re.finditer(rb"(?m)^STEPS INPUT ([^\n]+)", message))
    if not markers:
        return None
    source = markers[-1][1].decode("ascii")
    message = message[markers[-1].end():]
    if b"******** FAILED ********" not in message:
        return None
    name, assumption = book.admissions.get(source, (None, None))
    if not name:
        return None
    if b"Symbols in the main\nLisp package" in message and b"may not be defined or constrained" in message:
        reason = "ACL2 cannot introduce a function in COMMON-LISP"
    elif b"has a function definition in raw Common Lisp" in message:
        reason = "the host Lisp already defines the name"
    elif assumption:
        reason = f"ACL2 could not admit the event, and {assumption}"
    else:
        return None
    return source, f"{source} {name}: {reason}"


def proof_lines(book, failure=None, unavailable=None):
    counts = Counter()
    for proof_input, kind, name, first, qed, steps in book.proofs:
        missing = [book.uncertified[proof_input, n] for n in range(first, qed)
                   if (proof_input, n) in book.uncertified]
        reasons = list(dict.fromkeys(missing))
        omitted = len(missing)
        if unavailable:
            reasons = [unavailable]
            omitted = steps
        counts["proofs"] += 1
        counts["steps"] += steps
        if failure:
            status = "FAIL"
            certified = 0
            counts["failed"] += 1
        elif omitted:
            status = "unavailable"
            certified = steps - omitted
            counts["unavailable"] += 1
        else:
            status = "ok"
            certified = steps
            counts["certified"] += 1
        counts["certified_steps"] += certified
        count = f"{certified}/{steps}" if certified != steps else str(steps)
        explanation = " - " + ". ".join(reasons) if reasons else ""
        print(f"{status} {book.directory.relative_to(BUILD)} {kind} {native_symbol(name)} "
              f"{proof_input}:{first}-{qed} ({count} steps certified){explanation}", flush=True)
    for source, reason in book.omitted.items():
        if not any(r == reason for r in book.uncertified.values()):
            print(f"unadmitted {book.directory.relative_to(BUILD)} {reason}", flush=True)
    if failure:
        print(f"  {failure[0]}. See {failure[1]}.", flush=True)
        if not book.proofs:
            counts["failed"] += 1
    return counts


def certify_input(case, records, nodes):
    expected = {}
    for proof_input, path in zip(PROOF_INPUTS, case.inputs[2:]):
        with path.open("rb") as proofs:
            expected_proofs = expected_steps = 0
            for line in proofs:
                expected_proofs += line == b"(qed)\n"
                expected_steps += bool(STEP.match(line))
        expected[proof_input] = expected_proofs, expected_steps
    refused = {}
    while True:
        book = Book(case.out, records, nodes, refused)
        book.render()
        for proof_input, counts in expected.items():
            step_counts = [steps for source, *_, steps in book.proofs if source == proof_input]
            if (len(step_counts), sum(step_counts)) != counts:
                raise RuntimeError(f"The generated book did not account for every proof and step in {proof_input}.")
        packages = book.write()
        failure = certify_case(case, book, packages)
        if not failure:
            return proof_lines(book)
        message = failure[1].read_bytes()
        package = package_refusal(message)
        if package:
            return proof_lines(book, unavailable=f"{package}. See {failure[1]}")
        event = statement_refusal(book, message)
        if event is None or event[0] in refused:
            return proof_lines(book, failure=failure)
        source, reason = event
        attempt = case.out / f"refused-{len(refused) + 1}"
        for suffix in (".lisp", ".lsp", ".log"):
            shutil.copyfile((case.out / "book").with_suffix(suffix), attempt.with_suffix(suffix))
        refused[source] = reason + f" (see {attempt.with_suffix('.log')})"


def replay(cases, log):
    collect(cases, log)
    totals = Counter()
    for case in cases:
        try:
            verdict, records, nodes = read_trace(case.trace)
            other = js_verdict(case)
            if verdict != other or (case.expected is not None and verdict != case.expected):
                raise RuntimeError(f"Unexpected verdicts {verdict!r} and {other!r}.")
            if verdict != "accepted" and not verdict.startswith("provisional "):
                raise RuntimeError(f"The checkers give {verdict}.")
            totals.update(certify_input(case, records, nodes))
        except (OSError, RuntimeError, ValueError, subprocess.TimeoutExpired) as error:
            print(f"FAIL {case.name} {error}", flush=True)
            totals["failed"] += 1
        finally:
            clear_caches()
    return totals


def report(label, totals, elapsed):
    headline = "some proofs failed" if totals["failed"] else "all replayable proofs passed"
    print(f"{label}{headline} ({totals['certified']}/{totals['proofs']} proofs and "
          f"{totals['certified_steps']}/{totals['steps']} steps certified, "
          f"{totals['unavailable']} proofs unavailable, {totals['failed']} failed, "
          f"{elapsed:.2f} seconds)", flush=True)


def main(arguments):
    start = perf_counter()
    if len(arguments) not in (0, 3, 4):
        sys.exit("Usage: sh review/steps/run.sh [LIBRARY STATEMENTS PROOFS [LIBRARY-PROOFS]]")
    build_tools()
    if arguments:
        inputs = [Path(p) for p in arguments]
        if len(inputs) == 3:
            inputs.append(EMPTY)
        totals = replay([Case("input", inputs)], BUILD / "trace.log")
    else:
        group_start = perf_counter()
        totals = replay(list(specimens()), BUILD / "trace.log")
        report("Cases. ", totals, perf_counter() - group_start)
        group_start = perf_counter()
        source = self_input()
        counts = replay([source], BUILD / "self-trace.log")
        report("Checker source. ", counts, perf_counter() - group_start)
        totals.update(counts)
    report("", totals, perf_counter() - start)
    return bool(totals["failed"])


if __name__ == "__main__":
    os.environ["LC_ALL"] = "C"
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    try:
        sys.exit(main(sys.argv[1:]))
    except (OSError, RuntimeError) as error:
        sys.exit(str(error))
