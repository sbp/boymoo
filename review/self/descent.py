"""Proof recipes for built-in clauses, selectors, and changing measures."""

from library import CAR, CDR, COUNT, GAP, LEN, NATP, X, integer, lt, positive
from proof import CONSP, FALSE, IF, LESS, NOT, ONE, ORDINALP, QUOTE, compound, is_call, neg, write
from termination import RETURN_LAST


class Hypotheses:
    """Evidence from the signed tests above a call or a result branch."""

    def __init__(self, proof, tests, extra=()):
        self.proof = proof
        self.tests = tests
        self.extra = {step.first: step for step in extra}
        self.found = {}

    def find(self, term):
        if term in self.extra:
            return self.extra[term]
        if term in self.found:
            return self.found[term]
        for test, holds in self.tests:
            if (test if holds else neg(test)) == term:
                step = self.proof.assume(test, holds)
                self.found[term] = step
                return step
            if not holds:
                continue
            prefix, tail = [], test
            while is_call(tail, IF) and tail[3] == FALSE:
                prefix.append(tail[1])
                tail = tail[2]
            if term in prefix or term == tail:
                step = self.proof.assume(test)
                for conjunct in prefix:
                    first, step = self.proof.conjunct(step)
                    self.found.setdefault(conjunct, first)
                    if term == conjunct:
                        return self.found[term]
                self.found.setdefault(tail, step)
                return self.found[term]
        return None

    def require(self, term):
        step = self.find(term)
        if not step:
            raise ValueError("Missing hypothesis " + write(term).decode("ascii"))
        return step


def match_argument(pattern, term, bindings):
    """Match a built-in clause's one free variable to a term."""
    if pattern == X:
        if X not in bindings:
            bindings[X] = term
        return bindings[X] == term
    if not compound(pattern) or pattern[0] == QUOTE:
        return pattern == term
    return (compound(term) and len(pattern) == len(term) and pattern[0] == term[0]
            and all(match_argument(p, t, bindings) for p, t in zip(pattern[1:], term[1:])))


def direct_builtin(lib, clause, hypotheses=None):
    """Use an instance of a built-in clause whose tests are available."""
    goal = clause[-1]
    matches = []
    for index in range(1, 24):
        fact = lib.fact("built-in-clause-{}".format(index))
        bindings = {}
        if not match_argument(fact.first, goal, bindings):
            continue
        proof = lib.instantiate(fact, bindings.items())
        if set(proof.clause) <= set(clause):
            return proof
        matches.append(proof)
    if hypotheses:
        for proof in matches:
            result = proof
            for test in proof.clause[1:]:
                if test in clause:
                    continue
                evidence = hypotheses.find(test[1]) if is_call(test, NOT) else None
                if not evidence:
                    evidence = hypotheses.find(neg(test))
                if not evidence:
                    break
                result = lib.discharge(result, evidence)
            else:
                return result
    return None


def measure_ordinal(lib, measure):
    builtin = direct_builtin(lib, ((ORDINALP, measure),))
    if builtin:
        return builtin
    if measure[0] == GAP:
        return lib.cite("GAP-ORDINAL", measure[1:])
    return lib.cite("NATURAL-ORDINAL", (measure,), lib.natural(measure))


def selector_chain(lib, child, parent, hypotheses):
    """Prove a strict decrease along a selector path starting at a cons."""
    edges = []
    while child != parent and compound(child) and child[0] in (CAR, CDR):
        edges.append((child[0], child[1]))
        child = child[1]
    if child != parent or not edges:
        raise ValueError("Expected a selector path from " + write(parent).decode("ascii"))
    proof = None
    for head, base in reversed(edges):
        current, previous = (COUNT, (head, base)), (COUNT, base)
        cons = hypotheses.find((CONSP, base))
        if cons:
            builtin = lib.builtin(2 if head == CAR else 3, base)
            strict = lib.discharge(builtin, cons)
            bound = lib.rewrite(strict, lib.ordinal_comparison(current, previous))
        else:
            bound = lib.cite("COUNT-CAR-WEAK" if head == CAR else "COUNT-CDR-WEAK", (base,))
        proof = lib.compare_chain(bound, proof) if proof else bound
    assert proof.first[0] == LESS, proof.clause
    return proof


def selector_decrease(lib, goal, hypotheses):
    _, child, parent = goal
    assert child[0] == parent[0] == COUNT
    opened = lib.simplify(child[1], (), (RETURN_LAST,))
    actual = opened.first[2] if opened else child[1]
    if actual[0] in (CAR, CDR) and actual[1] == parent[1]:
        structural = lib.builtin(2 if actual[0] == CAR else 3, parent[1])
        step = lib.discharge(structural, hypotheses.require((CONSP, parent[1])))
    else:
        decrease = selector_chain(lib, actual, parent[1], hypotheses)
        step = lib.transport(decrease, lib.ordinal_comparison((COUNT, actual), parent))
    return lib.tidy(lib.rewrite(step, lib.symmetric(opened), (1, 1, 1))) if opened else step


def gap_decrease(lib, goal, hypotheses):
    _, smaller, measure = goal
    _, bound, old = measure
    _, unchanged_bound, new = smaller
    assert unchanged_bound == bound
    if is_call(bound, QUOTE):
        nat_old = hypotheses.require((NATP, old))
        int_old = lib.cite("NATURAL-INTEGER", (old,), nat_old)
        inside = hypotheses.require(lt(old, bound))
        advance = lib.cite("SUCCESSOR-LARGER", (old,), int_old)
        integers = (int_old,)
    else:
        n, p = bound[2], old
        int_n = hypotheses.require(integer(n))
        int_p = hypotheses.require(integer(p))
        p_positive = hypotheses.require(positive(p))
        n_at_least_p = hypotheses.require(neg(lt(n, p)))
        inside = lib.cite("LESS-THAN-NEXT", (n, p), int_n, int_p, n_at_least_p)
        advance = lib.cite("TENFOLD-LARGER", (p,), int_p, p_positive)
        integers = int_n, int_p
    return lib.cite("GAP-DECREASE", (bound, old, new),
                    lib.type_of(bound, integers), lib.type_of(old, integers),
                    lib.type_of(new, integers), inside, advance)


def shift(lib, proof, offset, left_offset=False):
    _, a, b = proof.first
    result = lib.cite("LESS-SHIFT", (a, b, offset),
                      lib.type_of(a), lib.type_of(b), lib.type_of(offset), proof)
    if left_offset:
        result = lib.rewrite(result, lib.axiom("COMMUTATIVITY-OF-+", a, offset), (1, 1))
        result = lib.rewrite(result, lib.axiom("COMMUTATIVITY-OF-+", b, offset), (1, 2))
    return lib.tidy(result)


def walk_decrease(lib, goal, hypotheses):
    _, child, parent = goal
    caller_walks, callee_walks = parent[0] != COUNT, child[0] != COUNT
    before = parent[2] if caller_walks else parent
    raw_after = child[2] if callee_walks else child
    assert caller_walks or not callee_walks
    opened = lib.simplify(raw_after, (), (RETURN_LAST,))
    after = opened.first[2] if opened else raw_after
    if after == before:
        assert caller_walks and not callee_walks
        proof = lib.cite("SUCCESSOR-LARGER", (before,), lib.type_of(before))
    else:
        proof = selector_chain(lib, after[1], before[1], hypotheses)
        if callee_walks:
            proof = shift(lib, proof, ONE, left_offset=True)
        elif caller_walks:
            growth = lib.cite("SUCCESSOR-LARGER", (before,), lib.type_of(before))
            proof = lib.compare_chain(proof, growth)
    if opened:
        proof = lib.rewrite_first(proof, lib.symmetric(opened))
    return lib.transport(proof, lib.ordinal_comparison(child, parent))


def run_decrease(lib, goal, hypotheses):
    _, child, parent = goal
    if child[1] == parent[1]:
        changed, unchanged = 2, 1
    else:
        changed, unchanged = 1, 2
    old = parent[changed][1]
    assert child[changed] == (LEN, (CDR, old)) and parent[unchanged] == child[unchanged]
    proof = lib.cite("LEN-CDR-LESS", (old,), hypotheses.require((CONSP, old)))
    proof = shift(lib, proof, parent[unchanged], left_offset=changed == 2)
    return lib.transport(proof, lib.ordinal_comparison(child, parent))
