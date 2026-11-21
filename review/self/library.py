"""Proof recipes for arithmetic and the size of trees and lists."""

from proof import (
    CONSP, FALSE, INTEGERP, LESS, MINUS, NIL, NOT, ONE, ORDINALP,
    ORDINAL_LESS, PLUS, QUOTE, RESULT, TIMES, TRUE, ZERO, Proof, cl, eq, is_call,
    ite, line, neg, proof_entry, quote, sym, write,
)

X, Y, Z = map(sym, ("X", "Y", "Z"))
NATP, NUMBERP, O_FINP, COUNT, LEN = map(
    sym, ("NATP", "ACL2-NUMBERP", "O-FINP", "ACL2-COUNT", "LEN")
)
CAR, CDR, RATIONALP = map(cl, ("CAR", "CDR", "RATIONALP"))
NFIX, GAP = map(sym, ("SELF-NFIX", "SELF-GAP"))
IMPLIES = sym("IMPLIES")


def plus(a, b):
    return PLUS, a, b


def minus(a):
    return MINUS, a


def diff(a, b):
    return plus(a, minus(b))


def lt(a, b):
    return LESS, a, b


def le(a, b):
    return neg(lt(b, a))


def positive(a):
    return lt(ZERO, a)


def nonnegative(a):
    return neg(lt(a, ZERO))


def guards(*terms):
    return tuple(neg(term) for term in terms)


def integer(term):
    return INTEGERP, term


class Library(Proof):
    def __init__(self):
        super().__init__()
        self.entries = []

    def lemma(self, name, claim, proof, *conditions):
        name = sym("SELF-" + name)
        clause = (claim,) + conditions
        self.entries.append(proof_entry("lemma", name, (name,) + clause,
                                        (self.subsume(proof, clause),)))
        assert name not in self.facts
        self.facts[name] = clause

    def definition(self, name, formals, body):
        self.add_definition(name, formals, body)
        source = line("define", NIL, (name, formals, body))
        self.entries.append(("define", name, [], source))

    def axiom(self, name, *args):
        return self.fact(sym(name), zip((X, Y, Z), args))

    def builtin(self, number, term):
        return self.fact("built-in-clause-{}".format(number), ((X, term),))

    def cite(self, name, args, *evidence):
        return self.use(sym("SELF-" + name), zip((X, Y, Z), args), evidence)

    def ints(self, *terms):
        return tuple(self.assume(integer(term)) for term in terms)

    def type_of(self, term, evidence=()):
        """Prove integrality from the supplied integer premises and closure."""
        literal = integer(term)
        for premise in evidence:
            if premise.first == literal:
                return premise
        if is_call(term, QUOTE) and isinstance(term[1], int):
            return self.prove(literal)
        if is_call(term, PLUS) or is_call(term, TIMES):
            name = "INTEGER-SUM" if term[0] == PLUS else "INTEGER-PRODUCT"
            return self.cite(name, term[1:], *(self.type_of(arg, evidence) for arg in term[1:]))
        if is_call(term, MINUS):
            return self.cite("INTEGER-NEGATION", term[1:], self.type_of(term[1], evidence))
        if is_call(term, COUNT):
            return self.cite("COUNT-INTEGER", term[1:])
        if is_call(term, LEN):
            return self.cite("LEN-INTEGER", term[1:])
        raise ValueError("Missing integer premise for " + write(term).decode("ascii"))

    def natural(self, term):
        if is_call(term, COUNT):
            return self.cite("COUNT-NATURAL", term[1:])
        if is_call(term, LEN):
            return self.cite("LEN-NATURAL", term[1:])
        if is_call(term, PLUS):
            return self.cite("NATURAL-SUM", term[1:], *(self.natural(arg) for arg in term[1:]))
        return self.prove((NATP, term), (), (NATP, NOT))

    def rational(self, term, evidence=()):
        return self.modus_ponens(self.axiom("INTEGER-IMPLIES-RATIONAL", term),
                                 self.type_of(term, evidence))

    def number(self, term, evidence=()):
        fact = self.fact("rationalp-acl2-numberp", ((X, term),))
        return self.modus_ponens(fact, self.rational(term, evidence))

    def logic_and_types(self):
        self.lemma("EXCLUDED-MIDDLE", neg(X), self.excluded_middle(X), X)
        self.lemma("IF-FALSE", eq(ite(X, Y, Z), Z), self.if_false(ite(X, Y, Z)), X)
        self.lemma("IF-TRUE", eq(ite(X, Y, Z), Y), self.if_true(ite(X, Y, Z)), neg(X))

        ix, iy = self.ints(X, Y)
        both = self.prove(ite(integer(X), integer(Y), FALSE), (ix, iy))
        for head, axiom, name in ((PLUS, "integerp-binary-+", "INTEGER-SUM"),
                                  (TIMES, "integerp-binary-*", "INTEGER-PRODUCT")):
            step = self.modus_ponens(self.fact(axiom), both)
            self.lemma(name, integer((head, X, Y)), step, *guards(integer(X), integer(Y)))
        step = self.modus_ponens(self.fact("integerp-unary--"), ix)
        self.lemma("INTEGER-NEGATION", integer(minus(X)), step, neg(integer(X)))

        nat = NATP, X
        nat_hyp = self.assume(nat)
        ix_from_nat, nonneg = self.conjunct(self.rewrite(nat_hyp, self.unfold(nat)))
        self.lemma("NATURAL-INTEGER", integer(X), ix_from_nat, neg(nat))
        self.lemma("NATURAL-NONNEGATIVE", nonnegative(X), nonneg, neg(nat))
        neg_x = self.assume(lt(X, ZERO), holds=False)
        self.lemma("NATURAL-FROM-BOUNDS", nat, self.prove(nat, (ix, neg_x), (NATP,)),
                   neg(integer(X)), lt(X, ZERO))

        cons = CONSP, X
        nonnumber = self.modus_ponens(self.fact("consp-not-acl2-numberp"), self.assume(cons))
        numeric = self.assume((NUMBERP, X))
        finite = self.front(self.cut(numeric, nonnumber), neg(cons))
        self.lemma("NUMBER-FINITE", (O_FINP, X),
                   self.prove((O_FINP, X), (finite,), (O_FINP, cl("ATOM"))), neg(numeric.first))
        self.lemma("INTEGER-FINITE", (O_FINP, X),
                   self.cite("NUMBER-FINITE", (X,), self.number(X, (ix,))), neg(integer(X)))

        x_finite = self.cite("INTEGER-FINITE", (X,), ix_from_nat)
        ordinal = ORDINALP, X
        self.lemma("NATURAL-ORDINAL", ordinal,
                   self.prove(ordinal, (x_finite, nat_hyp), (ORDINALP,)), neg(nat))
        finite_pair = (self.cite("INTEGER-FINITE", (X,), ix),
                       self.cite("INTEGER-FINITE", (Y,), iy))
        ordinal_lt = ORDINAL_LESS, X, Y
        self.lemma("FINITE-ORDER", eq(ordinal_lt, lt(X, Y)),
                   self.simplify(ordinal_lt, finite_pair, (ORDINAL_LESS, NOT)),
                   *guards(integer(X), integer(Y)))

        nfix = NFIX, X
        self.definition(NFIX, (X,), ite(nat, X, ZERO))
        fixed_nat = NATP, nfix
        good = self.transport_argument(nat_hyp, self.simplify(nfix, (nat_hyp,), (NFIX,)), 1)
        bad = self.transport_argument(
            self.prove((NATP, ZERO), (), (NATP, NOT)),
            self.simplify(nfix, (self.assume(nat, holds=False),), (NFIX,)), 1)
        self.lemma("NFIX-NATURAL", fixed_nat, self.cases(nat, good, bad))
        fixed = self.fact(sym("SELF-NFIX-NATURAL"))
        self.lemma("NFIX-INTEGER", integer(nfix), self.cite("NATURAL-INTEGER", (nfix,), fixed))
        self.lemma("NFIX-ORDINAL", (ORDINALP, nfix), self.cite("NATURAL-ORDINAL", (nfix,), fixed))
        self.definition(GAP, (X, Y), (NFIX, diff(X, Y)))
        gap = GAP, X, Y
        self.lemma("GAP-ORDINAL", (ORDINALP, gap),
                   self.transport_argument(self.cite("NFIX-ORDINAL", (diff(X, Y),)),
                                           self.unfold(gap), 1))

    def transport_argument(self, step, equality, index):
        return self.tidy(self.rewrite(step, self.symmetric(equality), (1, index)))

    def additive_identities(self):
        ix, = self.ints(X)
        left_zero = self.axiom("UNICITY-OF-0", X)
        fix = sym("FIX"), X
        left_zero = self.chain(left_zero, self.simplify(fix, (self.number(X, (ix,)),), (sym("FIX"),)))
        self.lemma("ADD-ZERO-LEFT", eq(plus(ZERO, X), X), left_zero, neg(integer(X)))
        self.lemma("ADD-ZERO-RIGHT", eq(plus(X, ZERO), X),
                   self.chain(self.axiom("COMMUTATIVITY-OF-+", X, ZERO), left_zero), neg(integer(X)))
        a, b, c = X, Y, Z
        step = self.symmetric(self.axiom("ASSOCIATIVITY-OF-+", a, b, c))
        step = self.rewrite(step, self.axiom("COMMUTATIVITY-OF-+", a, b), (1, 2, 1))
        step = self.chain(step, self.axiom("ASSOCIATIVITY-OF-+", b, a, c))
        self.lemma("ADD-SWAP", eq(plus(a, plus(b, c)), plus(b, plus(a, c))), step)

        def inverse_unique(a, b, sum_zero, integers):
            cancel = self.chain(self.axiom("COMMUTATIVITY-OF-+", minus(a), a),
                                self.axiom("INVERSE-OF-+", a))
            step = self.cite("ADD-ZERO-LEFT", (b,), self.type_of(b, integers))
            step = self.rewrite(step, self.symmetric(cancel), (1, 1, 1))
            step = self.chain(self.symmetric(step),
                              self.axiom("ASSOCIATIVITY-OF-+", minus(a), a, b))
            step = self.rewrite(step, sum_zero, (1, 2, 2))
            return self.chain(step, self.cite("ADD-ZERO-RIGHT", (minus(a),),
                                              self.type_of(minus(a), integers)))

        inverse = self.axiom("INVERSE-OF-+", X)
        reverse = self.chain(self.axiom("COMMUTATIVITY-OF-+", minus(X), X), inverse)
        involution = inverse_unique(minus(X), X, reverse, (ix,))
        self.lemma("DOUBLE-NEGATION", eq(minus(minus(X)), X), self.symmetric(involution),
                   neg(integer(X)))
        ints = self.ints(X, Y)
        a, b = plus(X, Y), plus(minus(X), minus(Y))
        zero_sum = self.linear_equal(plus(a, b), ZERO, ints)
        distribute = inverse_unique(a, b, zero_sum, ints)
        self.lemma("NEGATE-SUM", eq(minus(a), b), self.symmetric(distribute),
                   *guards(integer(X), integer(Y)))

    def push_minus(self, term, evidence):
        """Distribute unary minus over sums and remove double negatives."""
        if is_call(term, PLUS):
            result = self.reflexive(term)
            for index in (1, 2):
                arg = self.push_minus(term[index], evidence)
                if arg:
                    result = self.rewrite(result, arg, (1, 2, index))
            return result if result.first[2] != term else None
        if not is_call(term, MINUS):
            return None
        arg = term[1]
        if is_call(arg, QUOTE):
            return self.constant(term)
        double = sym("SELF-DOUBLE-NEGATION")
        distribute = sym("SELF-NEGATE-SUM")
        if is_call(arg, MINUS) and double in self.facts:
            result = self.cite("DOUBLE-NEGATION", (arg[1],), self.type_of(arg[1], evidence))
        elif is_call(arg, PLUS) and distribute in self.facts:
            result = self.cite("NEGATE-SUM", arg[1:],
                               *(self.type_of(item, evidence) for item in arg[1:]))
        else:
            return None
        return self.chain(result, self.push_minus(result.first[2], evidence))

    def linear_form(self, term, evidence):
        """Prove an equality to a sorted, right-associated integer sum."""
        def key(t):
            if is_call(t, QUOTE):
                return 0, b"", 0
            if is_call(t, MINUS):
                return 1, write(t[1]), 1
            return 1, write(t), 0

        def get(root, place):
            for index in place:
                root = root[index]
            return root

        step = self.push_minus(term, evidence) or self.reflexive(term)
        place = (1, 2)
        # Reassociate until every left summand is an atom of the sum.
        while is_call(get(step.first, place[1:]), PLUS):
            node = get(step.first, place[1:])
            if is_call(node[1], PLUS):
                a, b = node[1][1:]
                step = self.rewrite(step, self.axiom("ASSOCIATIVITY-OF-+", a, b, node[2]), place)
            else:
                place += (2,)

        changed = True
        while changed:
            changed = False
            place = (1, 2)
            while is_call(get(step.first, place[1:]), PLUS):
                a, rest = get(step.first, place[1:])[1:]
                suffix = is_call(rest, PLUS)
                b = rest[1] if suffix else rest
                if key(a) <= key(b):
                    place += (2,)
                    continue
                swap = (self.cite("ADD-SWAP", (a, b, rest[2])) if suffix
                        else self.axiom("COMMUTATIVITY-OF-+", a, b))
                step = self.rewrite(step, swap, place)
                changed = True
                place += (2,)

        place = (1, 2)
        while is_call(get(step.first, place[1:]), PLUS):
            a, rest = get(step.first, place[1:])[1:]
            suffix = is_call(rest, PLUS)
            b = rest[1] if suffix else rest
            combine = None
            if a == ZERO:
                step = self.rewrite(step, self.cite("ADD-ZERO-LEFT", (rest,),
                                                    self.type_of(rest, evidence)), place)
                continue
            if b == ZERO and not suffix:
                step = self.rewrite(step, self.cite("ADD-ZERO-RIGHT", (a,),
                                                    self.type_of(a, evidence)), place)
                continue
            if is_call(a, QUOTE) and is_call(b, QUOTE):
                combine = self.constant(plus(a, b))
            elif b == minus(a):
                combine = self.axiom("INVERSE-OF-+", a)
            elif a == minus(b):
                combine = self.chain(self.axiom("COMMUTATIVITY-OF-+", a, b),
                                     self.axiom("INVERSE-OF-+", b))
            if combine is None:
                place += (2,)
                continue
            if suffix:
                assoc = self.axiom("ASSOCIATIVITY-OF-+", a, b, rest[2])
                step = self.rewrite(step, self.symmetric(assoc), place)
            step = self.rewrite(step, combine, place + (1,) if suffix else place)
            # A cancellation can expose another pair to its left.
            place = (1, 2)
        return self.tidy(step)

    def linear_equal(self, left, right, integers):
        """Prove a sum identity by giving both sides the same normal form."""
        a = self.linear_form(left, integers)
        b = self.linear_form(right, integers)
        if a.first[2] != b.first[2]:
            raise ValueError("Different sum normal forms", write(a.first[2]), write(b.first[2]))
        return self.chain(a, self.symmetric(b))

    def comparison(self, a, b, integers):
        return self.cite("LESS-DIFFERENCE", (a, b), self.type_of(a, integers),
                         self.type_of(b, integers))

    def less_from_difference(self, a, b, positive_difference, integers):
        compare = self.comparison(a, b, integers)
        delta = self.linear_equal(diff(b, a), positive_difference.first[2], integers)
        return self.transport(positive_difference, self.rewrite(compare, delta, (1, 2, 2)))

    def weak_from_difference(self, a, b, nonnegative_difference, integers):
        compare = self.axiom("<-ON-OTHERS", b, a)
        delta = self.linear_equal(diff(b, a), nonnegative_difference.first[1][1], integers)
        compare = self.rewrite(compare, delta, (1, 2, 1))
        return self.transport_argument(nonnegative_difference, compare, 1)

    def ordered_arithmetic(self):
        ints = self.ints(X, Y)
        a = self.axiom("<-ON-OTHERS", X, Y)
        b = self.axiom("<-ON-OTHERS", ZERO, diff(Y, X))
        delta = self.linear_equal(diff(ZERO, diff(Y, X)), diff(X, Y), ints)
        b = self.rewrite(b, delta, (1, 2, 1))
        self.lemma("LESS-DIFFERENCE", eq(lt(X, Y), positive(diff(Y, X))),
                   self.chain(a, self.symmetric(b)), *guards(integer(X), integer(Y)))

        px, py = self.assume(positive(X)), self.assume(positive(Y))
        additive, multiplicative = self.conjunct(self.axiom("POSITIVE", X, Y))
        both_positive = ite(positive(X), positive(Y), FALSE)
        self.lemma("POSITIVE-SUM", positive(plus(X, Y)),
                   self.modus_ponens(additive, self.prove(both_positive, (px, py))),
                   *guards(positive(X), positive(Y)))
        r_x, r_y = (RATIONALP, X), (RATIONALP, Y)
        rx, ry = self.assume(r_x), self.assume(r_y)
        both_rational_positive = ite(r_x, ite(r_y, both_positive, FALSE), FALSE)
        self.lemma("POSITIVE-PRODUCT", positive((TIMES, X, Y)),
                   self.modus_ponens(multiplicative,
                                     self.prove(both_rational_positive, (rx, ry, px, py))),
                   *guards(r_x, r_y, positive(X), positive(Y)))

        ix = ints[0]
        tri, exclusive = self.conjunct(self.axiom("TRICHOTOMY", X))
        opposite = self.comparison(X, ZERO, (ix,))
        opposite = self.rewrite(opposite, self.linear_equal(diff(ZERO, X), minus(X), (ix,)),
                                (1, 2, 2))
        test = exclusive.first[1]
        exclusive = self.rewrite(exclusive, self.simplify(test, (px,), (NOT,)), (1, 1))
        exclusive = self.simplify_first(exclusive)
        self.lemma("POSITIVE-NONNEGATIVE", nonnegative(X),
                   self.transport_argument(exclusive, opposite, 1),
                   *guards(integer(X), positive(X)))

        goal = positive(plus(Y, X))
        good = self.cite("POSITIVE-SUM", (Y, X), py, px)
        x_zero = eq(X, ZERO)
        zero_case = self.transport_argument(py, self.cite("ADD-ZERO-RIGHT", (Y,), ints[1]), 2)
        zero_case = self.tidy(self.rewrite(zero_case, self.symmetric(self.assume(x_zero)),
                                          (1, 2, 2)))
        disjunction = self.modus_ponens(tri, self.number(X, (ix,)))
        negative_case = self.simplify_first(disjunction, (self.assume(positive(X), holds=False),
                                                         self.assume(x_zero, holds=False)))
        negative_case = self.transport(negative_case, opposite)
        contradiction = self.cut(negative_case, self.assume(lt(X, ZERO), holds=False))
        impossible = self.subsume(contradiction, (goal,) + contradiction.clause)
        result = self.cases(positive(X), good, self.cases(x_zero, zero_case, impossible))
        self.lemma("POSITIVE-PLUS-NONNEGATIVE", goal, result,
                   neg(integer(X)), neg(integer(Y)), neg(positive(Y)), lt(X, ZERO))

        goal = nonnegative(plus(Y, X))
        y_bound = self.assume(lt(Y, ZERO), holds=False)
        y_plus_x = self.type_of(plus(Y, X), ints)
        pos_sum = self.cite("POSITIVE-PLUS-NONNEGATIVE", (Y, X), ints[1], ix, px, y_bound)
        pos_sum = self.rewrite(pos_sum, self.axiom("COMMUTATIVITY-OF-+", X, Y), (1, 2))
        good = self.cite("POSITIVE-NONNEGATIVE", (plus(Y, X),), y_plus_x, pos_sum)
        y_zero = self.cite("ADD-ZERO-RIGHT", (Y,), ints[1])
        zero_case = self.tidy(self.rewrite(y_bound, self.symmetric(y_zero), (1, 1, 1)))
        zero_case = self.tidy(self.rewrite(zero_case, self.symmetric(self.assume(x_zero)),
                                          (1, 1, 1, 2)))
        impossible = self.subsume(contradiction, (goal,) + contradiction.clause)
        result = self.cases(positive(X), good, self.cases(x_zero, zero_case, impossible))
        self.lemma("NONNEGATIVE-SUM", goal, result,
                   neg(integer(X)), neg(integer(Y)), lt(X, ZERO), lt(Y, ZERO))

        nx = self.assume((NATP, X))
        ny = self.assume((NATP, Y))
        ix_nat, iy_nat = (self.cite("NATURAL-INTEGER", (p,), fact)
                          for p, fact in ((X, nx), (Y, ny)))
        x_nat_bound, y_nat_bound = (self.cite("NATURAL-NONNEGATIVE", (p,), fact)
                                   for p, fact in ((X, nx), (Y, ny)))
        sum_nat_bound = self.cite("NONNEGATIVE-SUM", (Y, X), iy_nat, ix_nat,
                                  y_nat_bound, x_nat_bound)
        sum_nat = self.cite("NATURAL-FROM-BOUNDS", (plus(X, Y),),
                            self.type_of(plus(X, Y), (ix_nat, iy_nat)), sum_nat_bound)
        self.lemma("NATURAL-SUM", (NATP, plus(X, Y)), sum_nat, neg(nx.first), neg(ny.first))

        pos_one = self.prove(positive(ONE))
        step = self.cite("POSITIVE-PLUS-NONNEGATIVE", (X, ONE), ix, self.type_of(ONE), pos_one,
                         self.assume(lt(X, ZERO), holds=False))
        self.lemma("POSITIVE-ONE-PLUS", positive(plus(ONE, X)), step,
                   neg(integer(X)), lt(X, ZERO))

        self.lemma("SUCCESSOR-LARGER", lt(X, plus(ONE, X)),
                   self.less_from_difference(X, plus(ONE, X), pos_one, (ix,)),
                   neg(integer(X)))

        compare_xy = lt(X, Y)
        nonless = self.assume(compare_xy, holds=False)
        delta = diff(X, Y)
        nonneg_delta = self.rewrite(nonless, self.axiom("<-ON-OTHERS", X, Y), (1, 1))
        bound = self.cite("POSITIVE-ONE-PLUS", (delta,), self.type_of(delta, ints), nonneg_delta)
        self.lemma("LESS-THAN-NEXT", lt(Y, plus(ONE, X)),
                   self.less_from_difference(Y, plus(ONE, X), bound, ints),
                   *guards(integer(X), integer(Y)), compare_xy)

        self.tenfold_increase(ix, px)

    def tenfold_increase(self, ix, px):
        nine, ten = quote(9), quote(10)
        times_x = TIMES, nine, X
        pos_product = self.cite("POSITIVE-PRODUCT", (nine, X), self.rational(nine),
                                self.rational(X, (ix,)), self.prove(positive(nine)), px)
        result = self.less_from_difference(X, plus(X, times_x), pos_product, (ix,))

        expansion = self.axiom("COMMUTATIVITY-OF-*", ten, X)
        expansion = self.rewrite(expansion, self.symmetric(self.compute(plus(ONE, nine), 10)),
                                 (1, 2, 2))
        expansion = self.chain(expansion, self.axiom("DISTRIBUTIVITY", X, ONE, nine))
        one_x = self.axiom("UNICITY-OF-1", X)
        one_x = self.chain(one_x, self.simplify((sym("FIX"), X),
                                               (self.number(X, (ix,)),), (sym("FIX"),)))
        x_one = self.chain(self.axiom("COMMUTATIVITY-OF-*", X, ONE), one_x)
        expansion = self.rewrite(expansion, x_one, (1, 2, 1))
        expansion = self.rewrite(expansion, self.axiom("COMMUTATIVITY-OF-*", X, nine), (1, 2, 2))
        self.lemma("TENFOLD-LARGER", lt(X, (TIMES, ten, X)),
                   self.transport_argument(result, expansion, 2),
                   *guards(integer(X), positive(X)))

    def order_lemmas(self):
        integers = self.ints(X, Y, Z)
        xy = self.assume(lt(X, Y))
        delta = self.rewrite(xy, self.comparison(X, Y, integers))
        bound = self.cite("POSITIVE-NONNEGATIVE", (diff(Y, X),),
                          self.type_of(diff(Y, X), integers), delta)
        self.lemma("LESS-TO-WEAK", le(X, Y), self.weak_from_difference(X, Y, bound, integers),
                   *guards(integer(X), integer(Y), lt(X, Y)))

        zero = self.axiom("ZERO")
        self.lemma("WEAK-REFLEXIVE", le(X, X), self.weak_from_difference(X, X, zero, integers),
                   neg(integer(X)))
        self.lemma("LESS-SHIFT", lt(plus(X, Z), plus(Y, Z)),
                   self.less_from_difference(plus(X, Z), plus(Y, Z), delta, integers),
                   *guards(integer(X), integer(Y), integer(Z), lt(X, Y)))

        for name, left_strict, right_strict in (
            ("LESS-TRANSITIVE", True, True),
            ("LESS-THEN-WEAK", True, False),
            ("WEAK-THEN-LESS", False, True),
        ):
            def delta_bound(a, b, strict):
                if strict:
                    proof = self.assume(lt(a, b))
                    eq_proof = self.comparison(a, b, integers)
                    return self.rewrite(proof, eq_proof), neg(lt(a, b))
                proof = self.assume(lt(b, a), holds=False)
                return self.rewrite(proof, self.axiom("<-ON-OTHERS", b, a), (1, 1)), lt(b, a)

            left, left_guard = delta_bound(X, Y, left_strict)
            right, right_guard = delta_bound(Y, Z, right_strict)
            a, b = diff(Y, X), diff(Z, Y)
            if left_strict and right_strict:
                delta = self.cite("POSITIVE-SUM", (a, b), left, right)
            else:
                known, positive_delta = (left, right) if right_strict else (right, left)
                low, high = (a, b) if right_strict else (b, a)
                delta = self.cite("POSITIVE-PLUS-NONNEGATIVE", (low, high),
                                  self.type_of(low, integers), self.type_of(high, integers),
                                  positive_delta, known)

            goal, step = lt(X, Z), self.less_from_difference(X, Z, delta, integers)
            self.lemma(name, goal, step, *guards(integer(X), integer(Y), integer(Z)),
                       left_guard, right_guard)

    def compare_chain(self, left, right):
        """Compose integer comparisons when at least one is strict."""
        p, q = left.first, right.first
        left_strict, right_strict = p[0] == LESS, q[0] == LESS
        a, b = p[1:] if left_strict else p[1][1:][::-1]
        middle, c = q[1:] if right_strict else q[1][1:][::-1]
        assert middle == b
        name = {
            (True, True): "LESS-TRANSITIVE",
            (True, False): "LESS-THEN-WEAK",
            (False, True): "WEAK-THEN-LESS",
        }[left_strict, right_strict]
        return self.cite(name, (a, b, c), *(self.type_of(t) for t in (a, b, c)), left, right)

    def as_weak(self, strict):
        _, a, b = strict.first
        return self.cite("LESS-TO-WEAK", (a, b), self.type_of(a), self.type_of(b), strict)

    def ordinal_comparison(self, a, b):
        return self.cite("FINITE-ORDER", (a, b), self.type_of(a), self.type_of(b))

    def length_lemmas(self):
        length, tail = (LEN, X), (LEN, (CDR, X))
        cons = CONSP, X
        main = NATP, length
        measure = COUNT, X
        descent = self.builtin(3, X)
        hypothesis = ite(descent.first, (NATP, tail), TRUE)
        child_nat = self.prove_if(self.assume(hypothesis), descent)

        opened = self.unfold(length)
        length_succ = self.chain(opened, self.if_true(opened.first[2]))
        length_zero = self.chain(opened, self.if_false(opened.first[2]))
        successor = self.cite("NATURAL-SUM", (ONE, tail), self.natural(ONE), child_nat)
        yes = self.transport_argument(successor, length_succ, 1)
        no = self.transport_argument(self.natural(ZERO), length_zero, 1)
        step = self.induct(self.builtin(1, X), self.cases(cons, yes, no), main, measure,
                           (((X, (CDR, X)),),))
        self.lemma("LEN-NATURAL", main, step)
        self.lemma("LEN-INTEGER", integer(length),
                   self.cite("NATURAL-INTEGER", (length,), self.natural(length)))

        less = self.cite("SUCCESSOR-LARGER", (tail,), self.type_of(tail))
        less = self.transport_argument(less, length_succ, 2)
        self.lemma("LEN-CDR-LESS", lt(tail, length), less, neg(cons))

    def count_lemmas(self):
        add, other = self.conjunct(self.axiom("CLOSURE", X, Y))
        _, other = self.conjunct(other)
        minus_number, _ = self.conjunct(other)
        self.lemma("SUM-NUMBER", (NUMBERP, plus(X, Y)), add)
        self.lemma("NEGATION-NUMBER", (NUMBERP, minus(X)), minus_number)

        def numeric(leaf, _tests):
            if is_call(leaf, PLUS):
                return self.cite("SUM-NUMBER", leaf[1:])
            if is_call(leaf, MINUS):
                return self.cite("NEGATION-NUMBER", leaf[1:])
            if is_call(leaf, integer_abs) or is_call(leaf, length):
                label = "ABS-NUMBER" if leaf[0] == integer_abs else "LENGTH-NUMBER"
                return self.cite(label, leaf[1:])
            evidence = (self.assume(integer(X)),) if leaf == X else ()
            return self.number(leaf, evidence)

        integer_abs, length = sym("INTEGER-ABS"), cl("LENGTH")
        template = NUMBERP, RESULT
        for function, name in ((integer_abs, "ABS-NUMBER"), (length, "LENGTH-NUMBER"),
                               (COUNT, "COUNT-NUMBER")):
            opened = self.unfold((function, X))
            proof = self.by_value(opened.first[2], template, numeric)
            self.lemma(name, (NUMBERP, (function, X)),
                       self.rewrite_result(proof, self.symmetric(opened), template))

        size = COUNT, X
        is_finite = self.cite("NUMBER-FINITE", (size,), self.cite("COUNT-NUMBER", (X,)))
        ordinal = self.builtin(1, X)
        step = self.simplify_first(ordinal, (is_finite,), (ORDINALP,))
        self.lemma("COUNT-NATURAL", (NATP, size), step)
        self.lemma("COUNT-INTEGER", integer(size),
                   self.cite("NATURAL-INTEGER", (size,), self.natural(size)))

    def weak_selectors(self):
        for head, name, number in (
            (CAR, "COUNT-CAR-WEAK", 2),
            (CDR, "COUNT-CDR-WEAK", 3),
        ):
            parent, child = (COUNT, X), (COUNT, (head, X))
            strict = self.rewrite(self.builtin(number, X), self.ordinal_comparison(child, parent))
            cons = CONSP, X
            yes = self.as_weak(strict)
            zero = self.cite("NATURAL-NONNEGATIVE", (parent,), self.natural(parent))
            completion = self.axiom("COMPLETION-OF-" + head[2].decode("ascii"), X)
            completion = self.chain(completion, self.if_false(completion.first[2]))
            child_zero = self.rewrite(self.reflexive(child), completion, (1, 2, 1))
            nil_size = self.simplify((COUNT, FALSE), (), (COUNT,))
            child_zero = self.chain(child_zero, nil_size)
            no = self.tidy(self.rewrite(zero, self.symmetric(child_zero), (1, 1, 2)))
            self.lemma(name, le(child, parent), self.cases(cons, yes, no))

    def integer_measures(self):
        ix, iy = self.ints(X, Y)
        pos_y, xy = self.assume(positive(Y)), self.assume(lt(X, Y))
        nonneg_y = self.cite("POSITIVE-NONNEGATIVE", (Y,), iy, pos_y)
        nat_y = self.cite("NATURAL-FROM-BOUNDS", (Y,), iy, nonneg_y)
        mx, my = (NFIX, X), (NFIX, Y)
        y_exact = self.simplify(my, (nat_y,), (NFIX,))
        nat_x = NATP, X
        x_exact = self.simplify(mx, (self.assume(nat_x),), (NFIX,))
        x_zero = self.simplify(mx, (self.assume(nat_x, holds=False),), (NFIX,))
        has_x = self.transport_argument(xy, x_exact, 1)
        has_x = self.transport_argument(has_x, y_exact, 2)
        lacks_x = self.transport_argument(pos_y, x_zero, 1)
        lacks_x = self.transport_argument(lacks_x, y_exact, 2)
        branch = self.cases(nat_x, has_x, lacks_x)
        ordinal_comparison = self.cite("FINITE-ORDER", (mx, my),
                                       self.cite("NFIX-INTEGER", (X,)),
                                       self.cite("NFIX-INTEGER", (Y,)))
        self.lemma("NFIX-DECREASE", (ORDINAL_LESS, mx, my),
                   self.transport(branch, ordinal_comparison),
                   *guards(integer(X), integer(Y), positive(Y), lt(X, Y)))

        # X is the upper bound. The lower endpoint moves from Y to Z.
        ints = self.ints(X, Y, Z)
        inside, advance = self.assume(lt(Y, X)), self.assume(lt(Y, Z))
        before, after = diff(X, Y), diff(X, Z)
        pos_before = self.tidy(self.rewrite(inside, self.comparison(Y, X, ints)))
        length_lost = self.tidy(self.rewrite(advance, self.comparison(Y, Z, ints)))
        smaller = self.less_from_difference(after, before, length_lost, ints)
        step = self.cite("NFIX-DECREASE", (after, before), self.type_of(after, ints),
                         self.type_of(before, ints), pos_before, smaller)
        after_gap, before_gap = (GAP, X, Z), (GAP, X, Y)
        step = self.transport_argument(step, self.unfold(after_gap), 1)
        step = self.transport_argument(step, self.unfold(before_gap), 2)
        self.lemma("GAP-DECREASE", (ORDINAL_LESS, after_gap, before_gap), step,
                   *guards(integer(X), integer(Y), integer(Z), lt(Y, X), lt(Y, Z)))

    def build(self):
        self.logic_and_types()
        self.additive_identities()
        self.ordered_arithmetic()
        self.order_lemmas()
        self.length_lemmas()
        self.count_lemmas()
        self.weak_selectors()
        self.integer_measures()
