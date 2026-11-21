"""Expand equality and propositional reasoning into Boymoo proof steps."""

import sys
from functools import lru_cache

sys.path.insert(0, "checks")
import reader


def freeze(datum):
    if isinstance(datum, (list, tuple)):
        return tuple(map(freeze, datum))
    return datum


def compound(datum):
    return isinstance(datum, tuple) and (not datum or not isinstance(datum[0], str))


def thaw(datum):
    if compound(datum):
        return list(map(thaw, datum)) if datum else NIL
    if isinstance(datum, tuple) and datum[0] == "dot":
        return ("dot", thaw(datum[1]))
    return datum


def write(datum):
    return reader.write(thaw(datum))


def line(word, *data):
    return b"(" + b" ".join([word.encode("ascii")] + [write(x) for x in data]) + b")\n"


def read_lines(path):
    with open(path, "rb") as source:
        for raw in source:
            word, data = reader.Reader(raw[:-1]).line()
            yield raw, word.decode("ascii"), freeze(data)


def sym(name, package="ACL2"):
    return ("sym", package.encode("ascii"), name.encode("ascii"))


def cl(name):
    return sym(name, "COMMON-LISP")


NIL, T, QUOTE = map(cl, ("NIL", "T", "QUOTE"))
IF, EQUAL, NOT, CONS, CONSP, INTEGERP, LESS = map(
    cl, ("IF", "EQUAL", "NOT", "CONS", "CONSP", "INTEGERP", "<")
)
PLUS, TIMES, MINUS, ORDINALP, ORDINAL_LESS = map(
    sym, ("BINARY-+", "BINARY-*", "UNARY--", "O-P", "O<")
)
RESULT = sym("SELF-RESULT")


def quote(datum):
    return QUOTE, datum


FALSE, TRUE, ZERO, ONE, NEG_ONE = map(quote, (NIL, T, 0, 1, -1))


def eq(a, b):
    return EQUAL, a, b


def neg(a):
    return NOT, a


def ite(test, yes, no):
    return IF, test, yes, no


def is_call(term, head):
    return compound(term) and term and term[0] == head


def subst(term, bindings):
    if not compound(term):
        return bindings.get(term, term)
    if term[0] == QUOTE:
        return term
    # A lambda binds every variable in its body. Only its actuals change.
    return (term[0],) + tuple(subst(arg, bindings) for arg in term[1:])


def change(term, place, old, new):
    if not place:
        assert term == old, (term, old)
        return new
    index = place[0]
    assert compound(term) and term[0] != QUOTE and 0 < index < len(term)
    return term[:index] + (change(term[index], place[1:], old, new),) + term[index + 1:]


class Step:
    """One inference and the clause it will produce."""

    __slots__ = ("word", "data", "clause")

    def __init__(self, word, data, clause):
        self.word = word
        self.data = data
        self.clause = clause

    @property
    def first(self):
        return self.clause[0]


def serialize(last):
    """Number the steps used by the conclusion, within this proof."""
    numbers, emitted, output = {}, {}, []

    def visit(step):
        if step not in numbers:
            args = [visit(arg) if isinstance(arg, Step) else arg for arg in step.data]
            source = line(step.word, *args)
            if source not in emitted:
                output.append(source)
                emitted[source] = len(output)
            numbers[step] = emitted[source]
        return numbers[step]

    visit(last)
    return output


def proof_entry(kind, name, fields, proofs):
    output = [line(kind, *fields)]
    counts = []
    for proof in proofs:
        steps = serialize(proof)
        counts.append(len(steps))
        output.extend(steps)
        output.append(line("qed"))
    return kind, name, counts, b"".join(output)


def unique(items):
    seen = set()
    result = []
    for item in items:
        if item not in seen:
            seen.add(item)
            result.append(item)
    return tuple(result)


class Proof:
    def __init__(self):
        self.facts = {}
        self.definitions = {}
        self.primitives = set()
        for _, word, data in read_lines("spec/ground.txt"):
            if word == "clause":
                self.facts[data[0]] = data[1:]
            elif word == "define":
                for definition in data[1:]:
                    self.add_definition(*definition)
            elif word == "primitive":
                self.primitives.add(data[0])

    def add_definition(self, name, formals, body):
        if formals == NIL:
            formals = ()
        self.definitions[name] = formals, body
        self.facts[name] = (eq((name,) + formals, body),)

    def fact(self, name, bindings=()):
        if isinstance(name, str):
            name = ("str", name.encode("ascii"))
        step = Step("fact", (name,), self.facts[name])
        return self.instantiate(step, bindings)

    def instantiate(self, step, bindings):
        pairs = tuple((v, t) for v, t in bindings if v != t)
        if not pairs:
            return step
        mapping = dict(pairs)
        assert len(mapping) == len(pairs)
        return Step("instantiate", (step, pairs),
                    tuple(subst(lit, mapping) for lit in step.clause))

    def use(self, name, bindings=(), evidence=()):
        step = self.fact(name, bindings)
        used = set()
        for premise in evidence:
            if premise.first not in used:
                step = self.discharge(step, premise)
                used.add(premise.first)
        return step

    def subsume(self, step, clause):
        clause = tuple(clause)
        if step.clause == clause:
            return step
        assert set(step.clause) - {FALSE} <= set(clause), (step.clause, clause)
        return Step("subsume", (step,) + clause, clause)

    def tidy(self, step):
        return self.subsume(step, unique(x for x in step.clause if x != FALSE))

    def front(self, step, literal):
        assert literal in step.clause
        return self.subsume(step, (literal,) + tuple(x for x in step.clause if x != literal))

    def cut(self, positive, negative):
        assert negative.first == neg(positive.first)
        return self.tidy(Step("cut", (positive, negative),
                              positive.clause[1:] + negative.clause[1:]))

    def rewrite(self, step, equality, place=(1,)):
        head, a, b = equality.first
        assert head == EQUAL
        index = place[0] - 1
        clause = (step.clause[:index]
                  + (change(step.clause[index], place[1:], a, b),)
                  + step.clause[index + 1:] + equality.clause[1:])
        return Step("substitute", (equality, step) + place, clause)

    def rewrite_first(self, step, equality):
        """Replace every occurrence of the left side in the first literal."""
        return self.rewrite_result(step, equality, step.first, equality.first[1])

    def rewrite_result(self, step, equality, template, slot=RESULT):
        """Rewrite just the positions marked by a slot in a literal template."""
        def places(term, place):
            if term == slot:
                yield place
            elif compound(term) and term[0] != QUOTE:
                for i, arg in enumerate(term[1:], 1):
                    yield from places(arg, place + (i,))

        for place in places(template, (1,)):
            step = self.rewrite(step, equality, place)
        return self.tidy(step)

    def beta(self, term):
        (_, formals, body), *args = term
        return Step("beta", (term,), (eq(term, subst(body, dict(zip(formals, args)))),))

    def compute(self, term, value):
        assert term[0] in self.primitives and all(is_call(a, QUOTE) for a in term[1:])
        return Step("compute", (term,), (eq(term, quote(value)),))

    def induct(self, ordinal, case, formula, measure, substitutions):
        def hypothesis(pairs):
            bindings = dict(pairs)
            smaller = ORDINAL_LESS, subst(measure, bindings), measure
            return neg(ite(smaller, subst(formula, bindings), TRUE))

        assert ordinal.clause == ((ORDINALP, measure),)
        case = self.subsume(case, tuple(map(hypothesis, substitutions)) + (formula,))
        return Step("induct", (ordinal, case, formula, measure, substitutions), (formula,))

    # Derived rules.

    def unfold(self, term):
        formals, _ = self.definitions[term[0]]
        assert len(formals) == len(term) - 1
        return self.fact(term[0], zip(formals, term[1:]))

    def reflexive(self, term):
        identity = self.fact("equal-same", ((sym("X"), term),))
        return self.true_from_eq(identity)

    def symmetric(self, equality):
        return self.rewrite(self.reflexive(equality.first[1]), equality, (1, 1))

    def chain(self, first, *rest):
        for equality in rest:
            if equality is not None:
                first = self.rewrite(first, equality, (1, 2))
        return self.tidy(first)

    def true_from_eq(self, equality):
        _, formula, value = equality.first
        assert value == TRUE
        step = self.fact("non-nil-true", ((sym("X"), formula),))
        step = self.rewrite(step, equality, (1, 1))
        return self.tidy(self.rewrite(step, self.compute(eq(TRUE, FALSE), NIL)))

    def nil_or_true(self, term):
        return self.fact("non-nil-true", ((sym("X"), term),))

    @lru_cache(maxsize=None)
    def not_nil(self):
        term = neg(FALSE)
        return self.true_from_eq(
            self.chain(self.unfold(term), self.compute(ite(FALSE, FALSE, TRUE), T)))

    @lru_cache(maxsize=512)
    def excluded_middle(self, term):
        # The equality in (x = nil, x) lets a proof of (not nil) give
        # (not x, x), by substituting x for nil.
        return self.tidy(self.rewrite(self.not_nil(), self.symmetric(self.nil_or_true(term)),
                                      (1, 1)))

    def assume(self, term, holds=True):
        lemma = sym("SELF-EXCLUDED-MIDDLE")
        if lemma in self.facts:
            excluded = self.fact(lemma, ((sym("X"), term),))
        else:
            excluded = self.excluded_middle(term)
        return self.front(excluded, term) if holds else excluded

    def discharge(self, step, evidence):
        """Resolve one side literal against an established literal."""
        main = step.first
        for side in step.clause[1:]:
            positive = side == neg(evidence.first)
            if not positive and evidence.first != neg(side):
                continue
            # An instance of excluded middle leaves this literal in place.
            if evidence.clause == (evidence.first, side):
                return step
            guard = self.front(step, side)
            result = self.cut(evidence, guard) if positive else self.cut(guard, evidence)
            return self.front(result, main)
        raise ValueError("The evidence does not discharge a side literal",
                         write(evidence.first), tuple(map(write, step.clause)))

    def if_false(self, term):
        _, test, yes, no = term
        lemma = sym("SELF-IF-FALSE")
        if lemma in self.facts:
            return self.fact(lemma, zip(map(sym, ("X", "Y", "Z")), (test, yes, no)))
        step = self.fact("if-nil", ((sym("Y"), yes), (sym("Z"), no)))
        return self.rewrite(step, self.symmetric(self.nil_or_true(test)), (1, 1, 1))

    def if_true(self, term):
        _, test, yes, no = term
        lemma = sym("SELF-IF-TRUE")
        if lemma in self.facts:
            return self.fact(lemma, zip(map(sym, ("X", "Y", "Z")), (test, yes, no)))
        step = self.fact("if-non-nil", zip(map(sym, ("X", "Y", "Z")), (test, yes, no)))
        nil_test = step.first
        test_is_nil = self.symmetric(self.assume(nil_test))
        # The conditional equality gives (not test) under (test = nil).
        not_nil = self.rewrite(self.not_nil(), test_is_nil, (1, 1))
        result = self.cut(step, self.front(not_nil, neg(nil_test)))
        return self.front(result, eq(term, yes))

    def select(self, term, evidence):
        test = term[1]
        if evidence.first == test:
            step = self.if_true(term)
        else:
            assert evidence.first == neg(test)
            step = self.if_false(term)
        return self.discharge(step, evidence)

    def prove_if(self, step, test_proof):
        return self.tidy(self.rewrite(step, self.select(step.first, test_proof)))

    def conjunct(self, step):
        """Extract both propositions from (if P Q 'nil)."""
        _, test, _, no = step.first
        assert no == FALSE
        test_proof = self.front(self.tidy(self.rewrite(step, self.if_false(step.first))), test)
        return test_proof, self.prove_if(step, test_proof)

    def modus_ponens(self, step, evidence):
        assert step.first[0] == sym("IMPLIES")
        reduced = self.prove_if(self.rewrite(step, self.unfold(step.first)), evidence)
        _, conclusion, yes, no = reduced.first
        assert (yes, no) == (TRUE, FALSE)
        return self.front(self.tidy(self.rewrite(reduced, self.if_false(reduced.first))), conclusion)

    def transport(self, step, equality):
        """Prove the left side of an equality from a proof of its right side."""
        return self.tidy(self.rewrite(step, self.symmetric(equality)))

    def cases(self, test, yes, no):
        """Join proofs of the same proposition under opposite hypotheses."""
        assert yes.first == no.first
        if neg(test) not in yes.clause:
            return yes
        if test not in no.clause:
            return no
        result = self.cut(self.front(no, test), self.front(yes, neg(test)))
        return self.front(result, yes.first)

    def by_value(self, value, template, leaf, tests=()):
        """Prove the instantiated template along each result path of a term."""
        if is_call(value, IF):
            test, yes, no = value[1:]
            yes_proof = self.by_value(yes, template, leaf, tests + ((test, True),))
            no_proof = self.by_value(no, template, leaf, tests + ((test, False),))
            yes_proof = self.rewrite_result(yes_proof, self.symmetric(self.if_true(value)), template)
            no_proof = self.rewrite_result(no_proof, self.symmetric(self.if_false(value)), template)
            return self.cases(test, yes_proof, no_proof)
        if compound(value) and compound(value[0]):
            equality = self.beta(value)
            opened = self.by_value(equality.first[2], template, leaf, tests)
            return self.rewrite_result(opened, self.symmetric(equality), template)
        step = leaf(value, tests)
        assert step.first == subst(template, {RESULT: value})
        return step

    def simplify(self, term, evidence=(), definitions=()):
        """Return a proof of a simplification, or None if it leaves the term alone."""
        if not compound(term) or term[0] == QUOTE:
            return None
        head = term[0]
        if compound(head):
            first = self.beta(term)
            return self.chain(first, self.simplify(first.first[2], evidence, definitions))
        if head in definitions:
            first = self.unfold(term)
            return self.chain(first, self.simplify(first.first[2], evidence, definitions))
        if head == IF:
            test = term[1]
            first = self.simplify(test, evidence, definitions)
            redex = (IF, first.first[2], term[2], term[3]) if first else term
            selected = None
            if redex[1] == FALSE:
                selected = self.fact("if-nil", zip(map(sym, ("Y", "Z")), redex[2:]))
            elif redex[1] == TRUE:
                selected = self.fact("if-non-nil", zip(map(sym, ("X", "Y", "Z")), redex[1:]))
                selected = self.front(selected, eq(redex, redex[2]))
                selected = self.tidy(self.rewrite(selected, self.compute(eq(TRUE, FALSE), NIL), (2,)))
            else:
                for premise in evidence:
                    if premise.first in (redex[1], neg(redex[1])):
                        selected = self.select(redex, premise)
                        break
            if first:
                selected = self.chain(self.rewrite(self.reflexive(term), first, (1, 2, 1)),
                                      selected)
            if not selected or selected.first[2] == redex:
                return selected
            return self.chain(selected, self.simplify(selected.first[2], evidence, definitions))

        result = None
        for index, arg in enumerate(term[1:], 1):
            equality = self.simplify(arg, evidence, definitions)
            if equality:
                if result is None:
                    result = self.reflexive(term)
                result = self.rewrite(result, equality, (1, 2, index))
        current = result.first[2] if result else term
        constant = self.constant(current)
        if constant is None:
            return result
        return self.chain(result, constant) if result else constant

    def constant(self, term):
        head, *args = term
        if head == EQUAL and args[0] == args[1]:
            return self.fact("equal-same", ((sym("X"), args[0]),))
        if not all(is_call(arg, QUOTE) for arg in args):
            return None
        values = [arg[1] for arg in args]
        if head == EQUAL:
            value = T if values[0] == values[1] else NIL
        elif head == CONSP:
            value = T if compound(values[0]) and values[0] else NIL
        elif head == INTEGERP:
            value = T if isinstance(values[0], int) else NIL
        elif head in (cl("RATIONALP"), cl("STRINGP"), sym("COMPLEX-RATIONALP")):
            tags = isinstance(values[0], tuple) and values[0] and values[0][0]
            recognized = {
                cl("RATIONALP"): tags == "ratio" or isinstance(values[0], int),
                cl("STRINGP"): tags == "str",
                sym("COMPLEX-RATIONALP"): tags == "complex",
            }
            value = T if recognized[head] else NIL
        elif head in (LESS, PLUS, MINUS, TIMES) and all(isinstance(x, int) for x in values):
            if head == LESS:
                value = T if values[0] < values[1] else NIL
            elif head == PLUS:
                value = values[0] + values[1]
            elif head == TIMES:
                value = values[0] * values[1]
            else:
                value = -values[0]
        else:
            return None
        return self.compute(term, value)

    def simplify_first(self, step, evidence=(), definitions=()):
        equality = self.simplify(step.first, evidence, definitions)
        return self.tidy(self.rewrite(step, equality)) if equality else step

    def prove(self, term, evidence=(), definitions=()):
        if term == TRUE:
            step = self.nil_or_true(TRUE)
            return self.tidy(self.rewrite(step, self.compute(eq(TRUE, FALSE), NIL)))
        for premise in evidence:
            if premise.first == term:
                return premise
        equality = self.simplify(term, evidence, definitions)
        if equality is None or equality.first[2] == term:
            raise ValueError("No proof of " + write(term).decode("ascii"))
        if equality.first[2] == TRUE:
            return self.true_from_eq(equality)
        return self.transport(self.prove(equality.first[2], evidence, definitions), equality)
