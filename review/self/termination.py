"""The walk and obligations of spec/logic.md, section 6."""

from collections import namedtuple
from itertools import product

from proof import IF, NIL, ORDINALP, ORDINAL_LESS, QUOTE, cl, compound, neg, quote, subst, sym, unique

ALL, LAMBDAS = (sym(name, "KEYWORD") for name in ("ALL", "LAMBDAS"))
RETURN_LAST = sym("RETURN-LAST")
MBE = quote(sym("MBE1-RAW"))
SELECTORS = {cl("CAR"), cl("CDR")}

Call = namedtuple("Call", "caller callee actuals tests")


def logical_body(term):
    """Keep the logical half of each mbe, including those in lambda bodies."""
    if not compound(term) or term[0] == QUOTE:
        return term
    head, args = term[0], term[1:]
    if head == RETURN_LAST and args[0] == MBE:
        return logical_body(args[2])
    if compound(head):
        head = head[:2] + (logical_body(head[2]),)
    return (head,) + tuple(logical_body(arg) for arg in args)


def recursive_calls(rulers, definitions):
    """Record calls in source order and carry signed tests through lambdas."""
    names = {definition[0] for definition in definitions}

    def extends(name):
        return rulers == ALL or (compound(rulers) and name in rulers)

    def walk(caller, term, tests, env, ruled=True):
        if not compound(term) or term[0] == QUOTE:
            return
        head, args = term[0], term[1:]
        if compound(head):
            _, formals, body = head
            for actual in args:
                yield from walk(caller, actual, tests, env, ruled and extends(LAMBDAS))
            bindings = dict(zip(formals, (subst(arg, env) for arg in args)))
            yield from walk(caller, body, tests, bindings, ruled)
        elif head == RETURN_LAST and args[0] == MBE:
            yield from walk(caller, args[2], tests, env, ruled)
        elif head == IF and ruled:
            test, yes, no = args
            yield from walk(caller, test, tests, env, extends(IF))
            literal = subst(test, env)
            yield from walk(caller, yes, tests + ((literal, True),), env)
            yield from walk(caller, no, tests + ((literal, False),), env)
        else:
            if head in names:
                yield Call(caller, head, tuple(subst(arg, env) for arg in args), tests)
            for arg in args:
                yield from walk(caller, arg, tests, env, ruled and extends(head))

    for name, _, body in definitions:
        yield from walk(name, body, (), {})


def obligation_cases(definitions, measures, calls):
    formals = {name: args for name, args, _ in definitions}
    for name, _, _ in definitions:
        yield ((ORDINALP, measures[name]),), None
    for call in calls:
        tests = tuple(neg(test) if holds else test for test, holds in call.tests)
        smaller = subst(measures[call.callee], dict(zip(formals[call.callee], call.actuals)))
        yield tests + ((ORDINAL_LESS, smaller, measures[call.caller]),), call


def obligations(definitions, measures, calls):
    return unique(clause for clause, _ in obligation_cases(definitions, measures, calls))


def selector_plan(definitions, calls):
    """Find a choice of one formal per function whose paths are all selectors."""
    formals = {name: () if args == NIL else args for name, args, _ in definitions}

    def selector_path(term, variable):
        if not compound(term) or term[0] not in SELECTORS:
            return False
        while compound(term) and term[0] in SELECTORS:
            term = term[1]
        return term == variable

    names = tuple(name for name, _, _ in definitions)
    actuals = [tuple(map(logical_body, call.actuals)) for call in calls]
    for indices in product(*(range(len(formals[name])) for name in names)):
        selected = dict(zip(names, indices))
        if all(selector_path(args[selected[call.callee]],
                             formals[call.caller][selected[call.caller]])
               for call, args in zip(calls, actuals)):
            return {name: formals[name][index] for name, index in selected.items()}
    return {}
