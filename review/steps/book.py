"""Translate the checker's trace into ACL2 events."""

from functools import lru_cache
import os
import sys

sys.path.insert(0, "checks")
from reader import Reader


def symbol(package, name):
    return ("sym", package.encode("latin-1"), name.encode("latin-1"))


NIL = symbol("COMMON-LISP", "NIL")
T = symbol("COMMON-LISP", "T")
QUOTE = symbol("COMMON-LISP", "QUOTE")
RULES = ("fact", "instantiate", "subsume", "cut", "substitute", "beta",
         "compute", "induct")
SHARE_AT = 4096


class Pair:
    """Conses in the trace share their children, even across proof steps."""

    __slots__ = ("car", "cdr", "size")

    def __init__(self, car, cdr):
        self.car, self.cdr = car, cdr
        self.size = min(SHARE_AT, 1 + datum_size(car) + datum_size(cdr))


def datum_size(value):
    return value.size if isinstance(value, Pair) else 1


def elements(value):
    while isinstance(value, Pair):
        yield value.car
        value = value.cdr
    if value != NIL:
        raise ValueError("A list in the trace has a dotted tail.")


def read_trace(path):
    nodes = []
    with path.open("rb") as trace:
        for text in trace:
            kind, args = Reader(text.rstrip(b"\n")).line()
            if kind == b"pair":
                car, cdr = args
                nodes.append(Pair(nodes[car], nodes[cdr]))
            elif kind == b"atom":
                nodes.append(args[0])
            elif kind == b"root":
                root = nodes[args[0]]
                return root.car[1].decode("ascii"), list(elements(root.cdr)), nodes
    raise ValueError("The checker trace has no root.")


def lisp_string(value):
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


def name_part(value):
    value = value.decode("latin-1")
    return "|" + value.replace("\\", "\\\\").replace("|", "\\|") + "|"


def native_symbol(value):
    if value == NIL:
        return "nil"
    if value == T:
        return "t"
    return name_part(value[1]) + "::" + name_part(value[2])


def lisp_list(items):
    return "(" + " ".join(items) + ")"


def write_lisp(path, forms):
    path.write_bytes(("\n".join(forms) + "\n").encode("latin-1"))


@lru_cache(maxsize=None)
def term_symbols(term, functions):
    found, seen, stack = set(), set(), [term]
    while stack:
        node = stack.pop()
        if not isinstance(node, Pair):
            if not functions:
                found.add(node)
            continue
        if node.car == QUOTE or node in seen:
            continue
        seen.add(node)
        stack.extend(elements(node.cdr))
        if functions:
            if isinstance(node.car, Pair):
                _, _, body = elements(node.car)
                stack.append(body)
            else:
                found.add(node.car)
    return frozenset(found)


def term_variables(term):
    return term_symbols(term, False)


def term_functions(term):
    return term_symbols(term, True)


def clear_caches():
    term_symbols.cache_clear()


class Book:
    def __init__(self, directory, records, nodes, refused):
        self.directory = directory
        self.records = records
        self.packages = {}
        used = {node[2] for node in nodes
                if isinstance(node, tuple) and node[:2] == ("sym", b"ACL2")}
        self.prefix = "BOYMOO-STEP-"
        while any(name.startswith(self.prefix.encode("ascii")) for name in used):
            self.prefix += "X"
        self.items = []
        self.pending = None
        self.definition = None
        self.entry = None
        self.proofs = []
        self.current = []
        self.obligations = []
        self.proof_steps = []
        self.measure_proofs = []
        self.function_names = {}
        self.choice_variables = {}
        self.native_constraint_hints = False
        self.expansion = False
        self.axioms = False
        self.source = ""
        self.refused = refused
        self.admissions = {}
        self.omitted = {}
        self.missing = {}
        self.uncertified = {}
        self.hidden = {}
        for rec in records:
            _, _, line, _ = elements(rec)
            word, *args = elements(line)
            if word[2] in (b"PACKAGE", b"HIDDEN-PACKAGE"):
                name, imports = args
                self.packages[name[1]] = (word[2] == b"HIDDEN-PACKAGE", imports)
        for name, (hidden, _) in self.packages.items():
            if hidden:
                self.hidden[name] = self.prefix + "SEED-" + str(len(self.hidden) + 1)

    def name(self, suffix):
        return self.prefix + str(suffix)

    def proof_name(self, proof_input, suffix):
        return self.name("LIBRARY-" + suffix if proof_input == "library-proofs" else suffix)

    def atom(self, value):
        if isinstance(value, int):
            return str(value)
        kind, *args = value
        if kind == "sym":
            if value[1] in self.hidden:
                seed = self.hidden[value[1]]
                name = lisp_string(value[2].decode("latin-1"))
                self.expansion = True
                return f",(intern-in-package-of-symbol {name} *{seed}*)"
            return native_symbol(value)
        if kind == "str":
            return lisp_string(args[0].decode("latin-1"))
        if kind == "ratio":
            return f"{args[0]}/{args[1]}"
        if kind == "complex":
            return "#c" + lisp_list(self.atom(a) for a in args)
        if kind == "char":
            self.expansion = True
            return f",(code-char {args[0]})"
        raise ValueError("An unknown kind of ACL2 datum in the trace.")

    def datum(self, value):
        stack, output = [value], []
        while stack:
            item = stack.pop()
            if isinstance(item, str):
                output.append(item)
            elif not isinstance(item, Pair):
                output.append(self.atom(item))
            else:
                parts = ["(", item.car]
                rest = item.cdr
                while isinstance(rest, Pair):
                    parts.extend((" ", rest.car))
                    rest = rest.cdr
                if rest != NIL:
                    parts.extend((" . ", rest))
                parts.append(")")
                stack.extend(reversed(parts))
        return "".join(output)

    def symbol_expression(self, value):
        text = self.atom(value)
        return text[1:] if text.startswith(",") else "'" + text

    def call(self, term, render):
        head = term.car
        if isinstance(head, Pair):
            formals, body = elements(head.cdr)
            name = f"(lambda {self.datum(formals)} {self.term(body)})"
        else:
            name = self.atom(self.function_names.get(head, head))
        return lisp_list([name, *(render(arg) for arg in elements(term.cdr))])

    def term(self, value):
        if not isinstance(value, Pair) or value.car == QUOTE:
            return self.datum(value)
        if datum_size(value) < SHARE_AT:
            return self.call(value, self.term)
        # Assign shared subterms in dependency order in the enclosing scope.
        incoming = {}
        bindings = {}
        forms = []

        def visit(term):
            if not isinstance(term, Pair) or term.car == QUOTE:
                return
            incoming[term] = incoming.get(term, 0) + 1
            if incoming[term] == 1:
                for arg in elements(term.cdr):
                    visit(arg)

        def render(term):
            if term in bindings:
                return bindings[term]
            if not isinstance(term, Pair) or term.car == QUOTE:
                return self.datum(term)
            form = self.call(term, render)
            if incoming[term] > 1:
                var = self.name("LET-" + str(len(forms) + 1))
                forms.append(f"({var} {form})")
                bindings[term] = var
                return var
            return form

        visit(value)
        form = render(value)
        return f"(let* ({' '.join(forms)}) {form})" if forms else form

    def clause(self, clause):
        lits = [self.term(term) for term in elements(clause)]
        if len(lits) == 1:
            return lits[0]
        return lisp_list(["or"] + lits) if lits else "nil"

    def emit(self, event):
        if self.expansion:
            event = f"(make-event (value `{event}))"
        self.expansion = False
        self.items.append((self.source, event))

    def reuse_or_admit(self, event, present, matches, reused="(value-triple :invisible)"):
        self.expansion = False
        self.emit(f"""(make-event
  (let ((world (w state)))
    (cond ((not {present}) (value `{event}))
          ({matches} (value `{reused}))
          (t (er soft 'steps "An existing ACL2 event differs from the library.")))))""")

    def unavailable(self, terms):
        for term in terms:
            for fn in sorted(term_functions(term)):
                if fn in self.missing:
                    return self.missing[fn]
        return None

    def omit(self, names, reason):
        self.omitted[self.source] = reason
        for name in names:
            self.missing[name] = reason
        self.expansion = False

    def admit(self, names, reason=None, terms=()):
        label = ", ".join(native_symbol(name) for name in names)
        self.admissions[self.source] = (label, reason)
        failed = self.refused.get(self.source) or self.unavailable(terms)
        if failed:
            self.omit(names, failed)
        return not failed

    def theorem(self, name, formula, *, use=(), extra="", theory=None, library_term=None):
        hints = []
        if use:
            hints.append(":use " + lisp_list(use))
        if theory:
            hints.append(":in-theory " + theory)
        if extra:
            hints.append(extra)
        text = f"(defthm {name} {formula}\n  :rule-classes nil"
        if hints:
            text += '\n  :hints (("Goal" ' + " ".join(hints) + "))"
        text += ")"
        if library_term is not None:
            stored = f"(getpropc `{name} 'theorem nil world)"
            matches = f"(equal {stored} `{self.datum(library_term)})"
            self.reuse_or_admit(text, stored, matches)
        else:
            self.emit(text)

    def define(self, args, measures=(), obligations=(), assumption=None, library=False):
        rulers, *definitions = args
        definitions = [list(elements(definition)) for definition in definitions]
        names = [fn for fn, _, _ in definitions]
        if not self.admit(names, assumption, [body for _, _, body in definitions] + list(measures)):
            return
        forms = []
        present, matches = [], []
        for i, (name, formals, body) in enumerate(definitions):
            decl = [":verify-guards nil", ":normalize nil",
                    ":ruler-extenders " + self.datum(rulers)]
            if measures:
                decl.append(":measure " + self.term(measures[i]))
                decl.append(":well-founded-relation o<")
            if i == 0 and obligations:
                theory = " :in-theory (theory 'minimal-theory)" if assumption is None else ""
                decl.append(':hints (("Goal" :use ' + lisp_list(obligations) + theory + "))")
            fn, formal_text, body = self.atom(name), self.datum(formals), self.datum(body)
            if library:
                known = f"(function-symbolp `{fn} world)"
                present.append(known)
                matches.append(f"(and {known} (not (programp `{fn} world))"
                               f" (equal (formals `{fn} world) `{formal_text})"
                               f" (equal (getpropc `{fn} 'unnormalized-body nil world) `{body}))")
            if measures:
                # The other branch fixes the single result signature for
                # definitions whose recursive calls are in tail position.
                body = f"(if t {body} nil)"
            forms.append(f"(defun {fn} {formal_text}\n"
                         f"  (declare (xargs {' '.join(decl)}))\n"
                         f"  {body})")
        text = forms[0] if len(forms) == 1 else "(mutual-recursion\n " + "\n ".join(forms) + ")"
        if library:
            self.reuse_or_admit(text, lisp_list(["or", *present]), lisp_list(["and", *matches]))
        else:
            self.emit(text)

    def constrain(self, args, witnesses=(), obligations=(), assumption=None, library=False):
        signatures, formulas = map(elements, args)
        signatures = [tuple(elements(sig)) for sig in signatures]
        formulas = [list(elements(formula)) for formula in formulas]
        intro = [fn for fn, _ in signatures] + [name for name, _ in formulas]
        if not self.admit(intro, assumption, [formula for _, formula in formulas]):
            return
        for fn, arity in signatures:
            if 2 * arity > self.addressable_memory():
                self.omit(intro, f"{self.source} requires an explicit signature for "
                          f"{native_symbol(fn)} with {arity} arguments")
                return
        for witness in witnesses:
            if witness in self.missing:
                self.omit(intro, self.missing[witness])
                return
        names = [self.atom(fn) for fn, _ in signatures]
        interface, local = [], []
        for i, (name, (_, arity)) in enumerate(zip(names, signatures)):
            interface.append(f"(({name}{' *' * arity}) => *)")
            formals = [self.name("ARG-" + str(j)) for j in range(arity)]
            formals_text = lisp_list(formals)
            if witnesses:
                call = lisp_list([self.atom(witnesses[i]), *formals])
                local.append(f"""(local (make-event
  (let* ((call '{call})
         (count (len (stobjs-out (car call) (w state))))
         (body (if (< 1 count) (list 'mv-list count call) call)))
    (value (list 'defun '{name} '{formals_text} body)))))""")
            else:
                local.append(f"(local (defun {name} {formals_text} nil))")
        exported = []
        for i, (name, formula) in enumerate(formulas):
            hint = ""
            if obligations and obligations[i]:
                enable = "(enable " + " ".join(names) + ")"
                hint = f' :hints (("Goal" :use ({obligations[i]}) :in-theory {enable}))'
            exported.append(f"(defthm {self.atom(name)} {self.term(formula)}"
                            f" :rule-classes nil{hint})")
        event = f"(encapsulate {lisp_list(interface)}\n " + "\n ".join(local + exported) + ")"
        if library:
            self.reuse_constraint(event, names, signatures, formulas)
        else:
            self.emit(event)

    def reuse_constraint(self, event, names, signatures, formulas):
        present = [f"(function-symbolp `{fn} world)" for fn in names]
        matches = [f"(and {known} (not (programp `{fn} world))"
                   f" (equal (len (formals `{fn} world)) {arity}))"
                   for fn, known, (_, arity) in zip(names, present, signatures)]
        facts = []
        if formulas:
            self.native_constraint_hints = True
        helper = self.name("CONSTRAINT-ORIGIN")
        for name, formula in formulas:
            native_name, native_term = self.atom(name), self.datum(formula)
            formula = self.term(formula)
            facts.append(f"""(make-event
  (let ((world (w state)))
    (if (equal (getpropc '{native_name} 'theorem nil world) '{native_term})
        (value '(value-triple :invisible))
      (mv-let (owner constraints origins)
        (constraint-info '{names[0]} world)
        (let* ((use (and owner ({helper} '{native_term} constraints origins)))
               (event '(defthm {native_name} {formula} :rule-classes nil)))
          (value (if use (append event (list :hints (list (list "Goal" :use use))))
                   event)))))))""")
        reused = lisp_list(["progn", *facts]) if facts else "(value-triple :invisible)"
        self.reuse_or_admit(event, lisp_list(["or", *present]), lisp_list(["and", *matches]), reused)

    @staticmethod
    def addressable_memory():
        try:
            pages, size = os.sysconf("SC_PHYS_PAGES"), os.sysconf("SC_PAGE_SIZE")
            if pages > 0 and size > 0:
                return min(sys.maxsize, pages * size)
        except (ValueError, OSError):
            pass
        return sys.maxsize

    def statement(self, word, args, pending, assumption=None, library=False):
        if word in ("package", "hidden-package", "reserve"):
            return
        if pending:
            self.pending = (self.source, word, args)
        elif word == "define":
            self.define(args, assumption=assumption, library=library)
        elif word == "constrain":
            self.constrain(args, assumption=assumption, library=library)
        elif word == "choose":
            fn, bound, free, body, free2 = args
            if not self.admit([fn], assumption, [body]):
                return
            strengthen = " :strengthen t" if free2 != NIL else ""
            if strengthen:
                self.choice_variables[fn] = (list(elements(bound)), list(elements(free)),
                                             list(elements(free2)))
            name = self.atom(fn)
            self.emit(f"(defchoose {name} {self.datum(bound)} {self.datum(free)}"
                      f" {self.datum(body)}{strengthen})")
        elif word == "axiom":
            if not self.admit(args[:1], assumption, args[1:]):
                return
            self.axioms = True
            name = self.atom(args[0])
            self.emit(f"(defaxiom {name} {self.term(args[1])} :rule-classes nil)")
        elif word == "theorem":
            if self.admit(args[:1], assumption, args[1:]):
                name, formula = self.atom(args[0]), self.term(args[1])
                self.theorem(name, formula, library_term=args[1] if library else None)

    def instance(self, premise, substitution):
        name, clause, _ = premise
        variables = frozenset().union(*(term_variables(x) for x in elements(clause)))
        bindings = [(var, term) for var, term in map(elements, elements(substitution))
                    if var in variables]
        if not bindings:
            return name
        return lisp_list([":instance", name,
                          *(f"({self.atom(var)} {self.term(term)})" for var, term in bindings)])

    def citation(self, name):
        if name not in self.choice_variables:
            return self.atom(name)
        bound, free, second = self.choice_variables[name]
        quoted = {v: self.symbol_expression(v) for v in bound + free + second}
        formals = lisp_list(["list", *(quoted[v] for v in free)])
        avoid = lisp_list(["list", *(quoted[v] for v in bound + free)])
        targets = lisp_list(["list", *(f"(list {quoted[v]})" for v in second)])
        self.expansion = True
        return (f"(:instance {self.atom(name)}"
                f" ,@(pairlis$ (generate-variable-lst-simple {formals} {avoid}) {targets}))")

    def induction(self, name, args):
        p, q, conclusion, measure, subs = args
        first, second = self.current[p - 1], self.current[q - 1]
        formula = self.term(conclusion)
        if subs == NIL:
            self.theorem(name, formula, use=(second[0],))
            return

        measure_text = self.term(measure)
        changed = term_variables(conclusion) | term_variables(measure)
        variables = sorted(frozenset().union(*(term_variables(term)
                                             for term in elements(second[1]))))
        variable_names = [self.atom(v) for v in variables]
        rank = name + "-RANK"
        scheme = name + "-SCHEME"
        lemma = name + "-INDUCTION"
        calls = []
        facts = [second[0]]
        for sub in elements(subs):
            substitution = {var: term for var, term in map(elements, elements(sub)) if var in changed}
            replacements = [self.term(substitution.get(v, v)) for v in variables]
            bind = [f"({var} {term})" for v, var, term in
                    zip(variables, variable_names, replacements) if v in substitution]
            new_measure = f"(let {lisp_list(bind)} {measure_text})" if bind else measure_text
            call = lisp_list([scheme, new_measure, *replacements])
            calls.append(f"(if (and (o-p {new_measure}) (o< {new_measure} {rank}))"
                         f" {call} nil)")
            facts.append(self.instance(first, sub))
        name_list = lisp_list([rank, *variable_names])
        self.emit(f"(defun {scheme} {name_list}\n"
                  f"  (declare (xargs :measure (if (o-p {rank}) {rank} 0)"
                  " :well-founded-relation o< :ruler-extenders :all :verify-guards nil))\n"
                  f"  (if (o-p {rank}) (list {' '.join(calls)}) nil))")
        induction = lisp_list([scheme, rank, *variable_names])
        self.emit(f"(defthm {lemma} (implies (equal {rank} {measure_text}) {formula})\n"
                  "  :rule-classes nil\n"
                  f'  :hints (("Goal" :induct {induction})\n'
                  f"          '(:use {lisp_list(facts)} :do-not-induct t)))")
        self.theorem(name, formula, use=(f"(:instance {lemma} ({rank} {measure_text}))",))

    def step(self, name, word, args, clause):
        formula = self.clause(clause)
        minimal = "(theory 'minimal-theory)"
        if word == "fact":
            citation = args[0]
            if citation[0] == "str":
                self.theorem(name, formula)
            else:
                self.theorem(name, formula, use=(self.citation(citation),))
        elif word == "instantiate":
            p, sub = args
            self.theorem(name, formula, use=(self.instance(self.current[p - 1], sub),),
                         theory=minimal)
        elif word == "subsume":
            self.theorem(name, formula, use=(self.current[args[0] - 1][0],), theory=minimal)
        elif word in ("cut", "substitute"):
            p, q = args[:2]
            extra = ":do-not-induct t"
            if word == "substitute":
                equality = next(elements(self.current[p - 1][1]))
                extra += f" :cases ({self.term(equality)})"
            self.theorem(name, formula,
                         use=(self.current[p - 1][0], self.current[q - 1][0]),
                         extra=extra, theory=minimal if word == "substitute" else None)
        elif word in ("beta", "compute"):
            self.theorem(name, formula, extra=":do-not-induct t")
        elif word == "induct":
            self.induction(name, args)
        self.current.append((name, clause, None))

    def replay_proof(self, proof_input, lines, prefix=""):
        self.current = []
        for source, number, word, args, clause in lines:
            self.source = source
            reason = self.unavailable(elements(clause))
            if not reason:
                if word == "fact":
                    reason = self.missing.get(args[0])
                elif word in ("instantiate", "subsume", "cut", "substitute", "induct"):
                    count = 1 if word in ("instantiate", "subsume") else 2
                    reason = next((self.current[n - 1][2] for n in args[:count]
                                   if self.current[n - 1][2]), None)
            if reason:
                self.current.append((None, clause, reason))
                if not prefix:
                    self.uncertified[proof_input, number] = reason
            else:
                self.step(self.proof_name(proof_input, prefix + str(number)), word, args, clause)
        return self.current[-1][0]

    def admit_measured(self, proof_input, args):
        source, _, definition = self.definition or self.pending
        functions = [(fn, len(list(elements(formals))))
                     for fn, formals, _ in map(elements, definition[1:])]
        function_set = {fn for fn, _ in functions}
        dependent = [
            any(term_functions(term) & function_set
                for _, _, _, _, clause in proof for term in elements(clause))
            for proof in self.measure_proofs]
        mapping = {}
        if any(dependent):
            number = self.measure_proofs[0][0][1]
            mapping = {fn: symbol("ACL2", self.proof_name(proof_input, f"ABSTRACT-{number}-{i}"))
                       for i, (fn, _) in enumerate(functions)}
            self.source = source
            self.emit("(local (encapsulate\n ("
                      + "\n  ".join(f"(({self.atom(mapping[fn])}{' *' * n}) => *)"
                                     for fn, n in functions) + ")\n "
                      + "\n ".join(f"(local (defun {self.atom(mapping[fn])}"
                                     f" {lisp_list(self.name(f'ARG-{j}') for j in range(n))} nil))"
                                     for fn, n in functions) + "))")
        obligations = []
        for proof, needs_abstraction in zip(self.measure_proofs, dependent):
            if needs_abstraction:
                self.function_names = mapping
                first = len(self.items)
                last = self.replay_proof(proof_input, proof, "ABSTRACT-")
                self.function_names = {}
                for i in range(first, len(self.items)):
                    position, event = self.items[i]
                    self.items[i] = (position, f"(local {event})")
                bindings = lisp_list(f"({self.atom(abstract)} {self.atom(fn)})"
                                     for fn, abstract in mapping.items())
                obligations.append(f"(:functional-instance {last} {bindings[1:-1]})" if last else None)
            else:
                obligations.append(self.replay_proof(proof_input, proof))
        self.source = source
        hint = "some Boymoo termination premises were unavailable" if None in obligations else None
        library = proof_input == "library-proofs" and self.definition is None
        self.define(definition, args[1:], [name for name in obligations if name], hint, library)
        for proof, needs_abstraction in zip(self.measure_proofs, dependent):
            if needs_abstraction:
                self.replay_proof(proof_input, proof)
        self.measure_proofs = []

    def qed(self, proof_input, number, source):
        kind, args, remaining = self.entry
        lines, self.proof_steps = self.proof_steps, []
        self.proofs.append((proof_input, kind, args[0], lines[0][1], number, len(lines)))
        if kind == "measure":
            self.measure_proofs.append(lines)
        else:
            last = self.replay_proof(proof_input, lines)
            self.obligations.append(last)
        if remaining > 1:
            self.entry = (kind, args, remaining - 1)
            return
        library = proof_input == "library-proofs"
        if kind in ("lemma", "theorem"):
            self.source = source
            if last:
                if self.admit(args[:1]):
                    term = self.pending[2][1] if library and kind == "theorem" else None
                    self.theorem(self.atom(args[0]), self.clause(lines[-1][-1]),
                                 use=(last,), library_term=term)
            else:
                self.omit(args[:1], self.uncertified[proof_input, lines[-1][1]])
        elif kind == "witness":
            self.source, _, pending_args = self.pending
            hint = "some Boymoo witness premises were unavailable" if None in self.obligations else None
            self.constrain(pending_args, args[1:], self.obligations, hint, library)
        elif kind == "measure":
            self.admit_measured(proof_input, args)
        self.obligations = []
        self.entry = None
        if self.definition:
            self.definition = None
        elif kind != "lemma":
            self.pending = None
        self.source = source

    def read_proofs(self, proof_input, number, word, args, detail):
        if word == "define":
            if detail != NIL:
                self.definition = (self.source, word, args)
            else:
                self.define(args)
        elif word == "choose":
            self.statement(word, args, False)
        elif word == "skip":
            self.source, kind, pending_args = self.definition or self.pending
            library = proof_input == "library-proofs" and self.definition is None
            assumption = "Boymoo took it from the library" if library else "Boymoo skipped its obligation"
            self.statement(kind, pending_args, False, assumption, library)
            if self.definition:
                self.definition = None
            else:
                self.pending = None
        elif word in ("theorem", "lemma", "measure", "witness"):
            self.entry = (word, args, len(list(elements(detail))))
        elif word == "qed":
            self.qed(proof_input, number, self.source)
        elif word in RULES:
            self.proof_steps.append((self.source, number, word, args, detail))

    def render(self):
        for record in self.records:
            source, number, line, detail = elements(record)
            source = source[2].decode("ascii").lower()
            word, *args = elements(line)
            word = word[2].decode("ascii").lower()
            self.source = f"{source}:{number} ({word})"
            if source in ("proofs", "library-proofs"):
                self.read_proofs(source, number, word, args, detail)
            else:
                library = source == "library"
                assumption = "Boymoo took it from the library" if library else None
                self.statement(word, args, detail != NIL, assumption, library)

    def package_events(self, hidden_open=False):
        events = []
        for name, (hidden, imports) in self.packages.items():
            if not hidden or hidden_open:
                if hidden_open:
                    expression = "'" + lisp_list(native_symbol(x) for x in elements(imports))
                else:
                    expression = lisp_list(["list", *(self.symbol_expression(x)
                                                      for x in elements(imports))])
                    self.expansion = False
                events.append(f"(defpkg {lisp_string(name.decode('latin-1'))} {expression})")
        return events

    def write(self):
        self.directory.mkdir(parents=True, exist_ok=True)
        header = '(in-package "ACL2")'
        helpers = []
        if self.native_constraint_hints:
            origin = self.name("CONSTRAINT-ORIGIN")
            helpers.append(f"""(local (defun {origin} (formula constraints origins)
  (declare (xargs :mode :program))
  (cond ((endp origins) nil)
        ((equal formula (car constraints))
         (if (eq (caar origins) :theorem) (car origins) (cadar origins)))
        (t ({origin} formula (cdr constraints) (cdr origins))))))""")
        write_lisp(self.directory / "book.lisp",
                   [header, "(set-ignore-ok t)", "(set-irrelevant-formals-ok t)",
                    "(set-bogus-mutual-recursion-ok t)"] + helpers +
                   [f'\n; {source}\n(value-triple (cw "~%STEPS INPUT {source}~%"))\n{event}'
                    for source, event in self.items])
        packages = self.package_events()
        if self.hidden:
            write_lisp(self.directory / "symbols.lisp",
                       [header] + [
                           f"(defconst *{seed}-OPEN* '{native_symbol(symbol(name.decode('latin-1'), 'ACL2-PKG-WITNESS'))})"
                           for name, seed in self.hidden.items()])
            write_lisp(self.directory / "hidden.lisp",
                       [header, '(local (include-book "symbols" :uncertified-okp nil'
                        ' :defaxioms-okp nil :skip-proofs-okp nil :ttags nil))'] + [
                            f"(make-event (list 'defconst '*{seed}* (list 'quote *{seed}-OPEN*)))"
                            for seed in self.hidden.values()])
        return packages
