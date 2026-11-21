"""Length proofs for the suffixes returned by the checker's lexer."""

from descent import Hypotheses, direct_builtin, selector_decrease
from library import CAR, CDR, COUNT, IMPLIES, LEN, le, lt
from proof import (
    CONS, CONSP, FALSE, LESS, NOT, ORDINAL_LESS, RESULT, TRUE, is_call,
    ite, neg, subst, sym, write,
)

PLAIN, QUOTED, PART, SYMBOL_REST, SHARP, ATOM = (
    sym("LEX-" + name, "BOYMOO")
    for name in ("PLAIN", "QUOTED", "PART", "SYMBOL-REST", "SHARP", "ATOM")
)
# Each result's suffix is reached by this many cdrs. For a symbol
# continuation, the input suffix is the last field of the package part.
FIELDS = {PLAIN: (1, 0), QUOTED: (2, 0), PART: (2, 0),
          SYMBOL_REST: (1, 2), SHARP: (1, 0), ATOM: (1, 0)}


def tail(term, n=1):
    for _ in range(n):
        term = CDR, term
    return term


def length(term):
    return LEN, term


class LexerProofs:
    def __init__(self, lib):
        self.lib = lib
        self.induction = None

    def cite(self, call, suffix=""):
        name, *args = call
        formals, _ = self.lib.definitions[name]
        lemma = sym("SELF-" + name[2].decode("ascii") + suffix)
        return self.lib.fact(lemma, zip(formals, args))

    def selectors(self, term):
        """Reduce selectors of explicit cons constructions."""
        lib = self.lib
        if term[0] not in (CAR, CDR):
            return None
        head, original = term
        inside = self.selectors(original)
        arg = inside.first[2] if inside else original
        if not is_call(arg, CONS):
            return lib.rewrite(lib.reflexive(term), inside, (1, 2, 1)) if inside else None
        kind = "CAR" if head == CAR else "CDR"
        selected = lib.axiom(kind + "-CONS", *arg[1:])
        if inside:
            selected = lib.chain(lib.rewrite(lib.reflexive(term), inside, (1, 2, 1)), selected)
        return lib.chain(selected, self.selectors(selected.first[2]))

    def replace_endpoint(self, proof, equality, lower):
        """Rewrite one endpoint of an integer length comparison."""
        if proof.first[0] == LESS:
            place = (1, 1 if lower else 2, 1)
        else:
            assert proof.first[0] == NOT and proof.first[1][0] == LESS
            place = (1, 1, 2 if lower else 1, 1)
        return self.lib.tidy(self.lib.rewrite(proof, equality, place))

    def relation(self, rest, source, hypotheses):
        lib = self.lib
        proof = None
        seen = set()
        current = rest
        while current != source:
            if current in seen:
                raise ValueError("Cycle in suffix of " + write(source).decode("ascii"))
            seen.add(current)
            smaller, parent = self.suffix_edge(current, hypotheses)
            if proof is not None:
                proof = lib.compare_chain(proof, smaller)
            else:
                proof = smaller
            current = parent
        if proof is None:
            return lib.cite("WEAK-REFLEXIVE", (length(source),), lib.type_of(length(source)))
        return proof

    def suffix_edge(self, rest, hypotheses):
        lib = self.lib
        selected, depth = rest, 0
        while is_call(selected, CDR):
            selected, depth = selected[1], depth + 1
        if depth and selected[0] in FIELDS and FIELDS[selected[0]][0] == depth:
            parent = tail(selected[1], FIELDS[selected[0]][1])
            comparison = self.lexed_suffix(selected, hypotheses)
            equation = self.selectors(parent)
            if equation:
                parent = equation.first[2]
                comparison = self.replace_endpoint(comparison, equation, lower=False)
            return comparison, parent
        if is_call(rest, CDR):
            parent = rest[1]
            cons = hypotheses.require((CONSP, parent))
            return lib.cite("LEN-CDR-LESS", (parent,), cons), parent
        raise ValueError("No suffix bound for " + write(rest).decode("ascii"))

    def lexed_suffix(self, call, hypotheses):
        lib = self.lib
        if self.induction and call[0] == self.induction[0]:
            _, formals, formula, measure, substitutions = self.induction
            bindings = tuple((v, t) for v, t in zip(formals, call[1:]) if v != t)
            sub = dict(bindings)
            if bindings not in substitutions:
                substitutions.append(bindings)
            goal = ORDINAL_LESS, subst(measure, sub), measure
            smaller = direct_builtin(lib, (goal,), hypotheses)
            if smaller is None:
                smaller = selector_decrease(lib, goal, hypotheses)
            ih = ite(goal, subst(formula, sub), TRUE)
            formula_proof = lib.prove_if(lib.assume(ih), smaller)
        elif call[0] == PLAIN:
            started = self.plain_test(call, hypotheses)
            if started:
                return lib.discharge(self.cite(call, "-STRICT"), started)
            return self.cite(call, "-UPPER")
        else:
            formula_proof = self.cite(call, "-STRICT")
        if call[0] == PLAIN:
            return formula_proof
        return lib.modus_ponens(formula_proof, hypotheses.require(call))

    def plain_test(self, call, hypotheses):
        """Find evidence that the plain scan consumes its first character."""
        lib = self.lib
        opened = lib.unfold(call)
        body = opened.first[2]
        test = body[1]
        evidence = hypotheses.find(test)
        if evidence:
            return evidence
        cons, plain = (hypotheses.find(term) for term in test[1:3])
        if cons and plain:
            return lib.prove(test, (cons, plain))
        if call[2] != FALSE:
            return None
        run = hypotheses.find((CONSP, (CAR, call)))
        if run is None:
            return None
        # With an empty accumulator, the branch that consumes nothing has
        # a nil run. The nonempty run therefore implies the starting test.
        empty = lib.chain(opened, lib.if_false(body))
        run = lib.rewrite(run, empty, (1, 1, 1))
        projection = self.selectors(run.first[1])
        run = lib.rewrite(run, projection, (1, 1))
        run = lib.rewrite(run, lib.compute(run.first, FALSE[1]))
        return lib.front(lib.tidy(run), test)

    def implication(self, antecedent, result):
        lib = self.lib
        formula = IMPLIES, antecedent, result.first
        unfolded = lib.unfold(formula)
        yes = lib.chain(unfolded, lib.if_true(unfolded.first[2]))
        yes = lib.chain(yes, lib.select(yes.first[2], result))
        no = lib.chain(unfolded, lib.if_false(unfolded.first[2]))
        return lib.cases(antecedent, lib.true_from_eq(yes), lib.true_from_eq(no))

    def result_branch(self, function, source, value, tests, template):
        lib = self.lib
        if value == FALSE:
            return lib.prove(subst(template, {RESULT: value}), (), (IMPLIES,))
        weak = function == PLAIN
        nonempty = () if weak else (lib.assume(value),)
        hypotheses = Hypotheses(lib, tests, nonempty)
        rest = tail(value, FIELDS[function][0])
        equation = self.selectors(rest)
        actual = equation.first[2] if equation else rest
        bound = self.relation(actual, source, hypotheses)
        if weak and bound.first[0] == LESS:
            bound = lib.as_weak(bound)
        if equation:
            bound = self.replace_endpoint(bound, lib.symmetric(equation), lower=True)
        return bound if weak else self.implication(value, bound)

    def prove_result(self, function, induct=False):
        lib = self.lib
        formals, _ = lib.definitions[function]
        call = (function,) + formals
        depth, offset = FIELDS[function]
        right = tail(formals[0], offset)
        left = tail(RESULT, depth)
        if function == PLAIN:
            template = le(length(left), length(right))
            suffix = "-UPPER"
        else:
            template = IMPLIES, RESULT, lt(length(left), length(right))
            suffix = "-STRICT"
        formula = subst(template, {RESULT: call})
        if induct:
            measure = COUNT, formals[0]
            substitutions = []
            self.induction = function, formals, formula, measure, substitutions
        unfolded = lib.unfold(call)

        def leaf(value, tests):
            return self.result_branch(function, right, value, tests, template)

        result = lib.by_value(unfolded.first[2], template, leaf)
        result = lib.rewrite_result(result, lib.symmetric(unfolded), template)
        if induct:
            result = lib.induct(lib.builtin(1, formals[0]), result, formula, measure,
                                tuple(substitutions))
            self.induction = None
        lib.lemma(function[2].decode("ascii") + suffix, formula, result)

    def prove_plain_strict(self):
        lib = self.lib
        formals, _ = lib.definitions[PLAIN]
        call = (PLAIN,) + formals
        equation = lib.unfold(call)
        test, again, _ = equation.first[2][1:]
        hypotheses = Hypotheses(lib, ((test, True),))
        step = self.relation(tail(again), formals[0], hypotheses)
        unfolded = lib.chain(equation, lib.if_true(equation.first[2]))
        step = lib.rewrite(step, lib.symmetric(unfolded), (1, 1, 1, 1))
        goal = lt(length(tail(call)), length(formals[0]))
        lib.lemma("LEX-PLAIN-STRICT", goal, step, neg(test))

    def build(self):
        self.prove_result(PLAIN, induct=True)
        self.prove_plain_strict()
        self.prove_result(QUOTED, induct=True)
        for function in (PART, SYMBOL_REST, SHARP, ATOM):
            self.prove_result(function)

    def decrease(self, goal, hypotheses):
        _, child, parent = goal
        return self.lib.transport(self.relation(child[1], parent[1], hypotheses),
                                  self.lib.ordinal_comparison(child, parent))
