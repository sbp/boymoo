"""Write the checker's proof entries in the order of its statements."""

import sys

from descent import (
    Hypotheses, direct_builtin, gap_decrease, measure_ordinal, run_decrease,
    selector_decrease, walk_decrease,
)
from lexer import LexerProofs
from library import COUNT, GAP, LEN, Library, plus
from proof import ONE, line, proof_entry, quote, read_lines, unique, write
from termination import logical_body, obligation_cases, obligations, recursive_calls, selector_plan


DECREMENTS = {
    b"NTH-ELEM": 0, b"REPLACE-NTH": 0, b"BUMP": 0, b"MV-NTH-TERMS": 1,
    b"STRING-CHARS": 2, b"STRING-LINES": 3,
}
INCREMENTS = {b"DIGIT-COUNT": (2, 9), b"SIXTEENS": (1, 15)}


def measures_for(definitions, calls):
    name, formals, _ = definitions[0]
    label = name[2]
    if label in DECREMENTS:
        return {name: (COUNT, formals[DECREMENTS[label]])}
    if label in INCREMENTS:
        index, bound = INCREMENTS[label]
        return {name: (GAP, quote(bound), formals[index])}
    if label == b"TENS-UP-TO":
        return {name: (GAP, plus(ONE, formals[0]), formals[1])}
    if label == b"RUN":
        return {name: plus((LEN, formals[0]), (LEN, formals[2]))}
    if label == b"WALK":
        return {fn: plus(ONE, (COUNT, args[0])) if fn[2].startswith(b"WALK")
                else (COUNT, args[0]) for fn, args, _ in definitions}
    if label == b"PARSE-LOOP":
        return {name: (LEN, formals[0])}
    selectors = selector_plan(definitions, calls)
    if not selectors:
        raise ValueError("No measure for " + text(name))
    return {fn: (COUNT, arg) for fn, arg in selectors.items()}


def prove_definition(lib, definitions, measures, calls, lexer=None):
    name = definitions[0][0]
    proofs, proved = [], set()
    for clause, call in obligation_cases(definitions, measures, calls):
        if clause in proved:
            continue
        proved.add(clause)
        if not call:
            proof = measure_ordinal(lib, clause[0][1])
        else:
            tests = Hypotheses(lib, call.tests)
            proof = direct_builtin(lib, clause, tests)
            if proof is None:
                goal = clause[-1]
                if goal[2][0] == GAP:
                    proof = gap_decrease(lib, goal, tests)
                elif name[2] == b"RUN":
                    proof = run_decrease(lib, goal, tests)
                elif name[2] == b"WALK":
                    proof = walk_decrease(lib, goal, tests)
                elif lexer:
                    proof = lexer.decrease(goal, tests)
                else:
                    proof = selector_decrease(lib, goal, tests)
        proofs.append(lib.subsume(proof, clause))
    fields = (name,) + tuple(measures[fn] for fn, _, _ in definitions)
    return proof_entry("measure", name, fields, proofs)


def generate(statements, baseline, directory, logical):
    lib = Library()
    lib.build()
    entries = list(lib.entries)
    recursive, changed, logical_lines = [], [], []
    seen = {}
    for raw, word, data in read_lines(statements):
        if word != "define":
            logical_lines.append(raw)
            continue
        if raw in seen:
            logical_lines.append(seen[raw])
            continue
        rulers, definitions = data[0], data[1:]
        stripped = tuple((fn, args, logical_body(body)) for fn, args, body in definitions)
        changed_names = tuple(old[0] for old, new in zip(definitions, stripped) if old != new)
        seen[raw] = line("define", rulers, *stripped) if changed_names else raw
        logical_lines.append(seen[raw])

        calls = tuple(recursive_calls(rulers, definitions))
        if not calls:
            for definition in stripped if logical else definitions:
                lib.add_definition(*definition)
            if changed_names:
                changed.append((changed_names, 0, 0, 0))
            continue
        name = definitions[0][0]
        recursive.append(name)
        measures = measures_for(definitions, calls)
        if changed_names:
            plain_calls = tuple(recursive_calls(rulers, stripped))
            raw_clauses = obligations(definitions, measures, calls)
            plain_clauses = obligations(stripped, measures, plain_calls)
            normalized = unique(tuple(map(logical_body, clause)) for clause in raw_clauses)
            if normalized != plain_clauses:
                raise ValueError("Different logical obligations for " + text(name))
            differences = sum(a != b for a, b in zip(raw_clauses, plain_clauses))
            differences += abs(len(raw_clauses) - len(plain_clauses))
            changed.append((changed_names, len(raw_clauses), len(plain_clauses), differences))
        accepted_definitions = stripped if logical else definitions
        if logical:
            calls = tuple(recursive_calls(rulers, stripped))
        lexer = None
        if name[2] == b"PARSE-LOOP":
            first_lemma = len(lib.entries)
            lexer = LexerProofs(lib)
            lexer.build()
            entries.extend(lib.entries[first_lemma:])
        entries.append(prove_definition(lib, accepted_definitions, measures, calls, lexer))
        for definition in accepted_definitions:
            lib.add_definition(*definition)

    baseline_names = tuple(data[0] for _, word, data in read_lines(baseline) if word == "skip")
    if tuple(recursive) != baseline_names:
        raise ValueError("The recursive statements differ from the all-skip entries")
    if logical:
        with open(directory + "/logical.statements", "wb") as out:
            out.writelines(logical_lines)
    stem = "logical" if logical else "checker"
    with open(directory + "/" + stem + ".proofs", "wb") as out:
        for _, _, _, source in entries:
            out.write(source)
    if not logical:
        with open(directory + "/sizes.tsv", "w") as out:
            print("entry\tname\tproofs\tsteps per proof\tsteps\tentry bytes", file=out)
            for kind, name, counts, source in entries:
                print(kind, text(name), len(counts), ",".join(map(str, counts)), sum(counts),
                      len(source), sep="\t", file=out)
        with open(directory + "/mbe.tsv", "w") as out:
            print("functions with mbe\tobligations\tlogical obligations\tchanged clauses",
                  file=out)
            for names, raw_count, plain_count, differences in changed:
                print(",".join(map(text, names)), raw_count, plain_count, differences,
                      sep="\t", file=out)


def text(datum):
    return write(datum).decode("ascii")


def ground_functions():
    names = (text(definition[0]) for _, word, data in read_lines("spec/ground.txt")
             if word == "define" for definition in data[1:])
    print("(assign bx-ground-fns '({}))".format(" ".join(names)))


if __name__ == "__main__":
    if sys.argv[1:] == ["ground-functions"]:
        ground_functions()
    elif len(sys.argv) == 4:
        generate(*sys.argv[1:], logical=False)
    elif len(sys.argv) == 5 and sys.argv[4] == "logical":
        generate(*sys.argv[1:4], logical=True)
    else:
        sys.exit("Usage: python3 -B review/self/pilot.py STATEMENTS ALL-SKIPS DIRECTORY [logical]")
