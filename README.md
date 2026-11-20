# Boymoo

Boymoo is an independent checker for the [ACL2](https://www.cs.utexas.edu/~moore/acl2/) theorem prover. It has two goals.

1. **A checker small enough to audit.** It accepts a theorem only with a proof written out in primitive steps, and it does not rest on ACL2's own word that the theorem is proved.
2. **Durability.** A proof can be checked with a small stack of software that contains neither ACL2 nor Common Lisp.

Its watchwords are that it be auditable, minimal and efficient, and that it reuse as much existing ACL2 work as it can: every book that ACL2 can load is to become input for it.

## How it works

ACL2 is the front end. It reads a book, expands every macro, and writes what the book states as plain **statements**: definitions, theorems, axioms, functions introduced by constraint or by choice, and packages. What remains of ACL2's language after that expansion is small: seven kinds of data, 32 primitive functions, terms, and eight kinds of statement. This repository calls it **ACL2 Core**. ACL2's documentation names the parts, translated terms and primitive event macros; the name for the whole is this project's.

ACL2 is the definition of ACL2. Wherever ACL2 decides something, by its axioms, by its evaluator or by the tests it makes before it admits an event, ACL2 Core decides the same, and a check confirms it against ACL2.

A **checker** reads three things: a library of statements that are taken as given, the statements of a book, and a file of proofs. It answers with one line:

- `accepted`: every theorem follows, by eight rules of inference, from ACL2's axioms and the book's own statements;
- `provisional`, with four counts: the same, except for the proofs that were skipped, the axioms that were assumed, and the definitions and facts of the library that were given;
- `rejected`, with the place of the first line that fails.

ACL2 says what a book states and is used to cross-check. It takes no part in finding or checking a proof.

## What is in the repository

The repository holds the specification, and the checks that compare it with ACL2. No checker has been written yet; [`PLAN.md`](PLAN.md) gives the order of the work.

| Path | What it is |
|---|---|
| [`spec/language.md`](spec/language.md) | The language: data, the 32 primitive functions and their value on every input, running and attachments, terms, names, the eight kinds of statement, and what each kind of ACL2 event becomes. |
| [`spec/logic.md`](spec/logic.md) | The logic: the axioms, the eight rules with the argument that each is sound, how each statement is admitted and what must be proved for it, what a verdict means, with the argument for it, and where ACL2 Core follows ACL2 and where it cannot. |
| [`spec/formats.md`](spec/formats.md) | The interchange formats: the text of data, statements and proofs, the order of checking, the budgets, and the three verdict lines. |
| [`spec/ground.txt`](spec/ground.txt) | The ground theory that every checker holds: ACL2's packages, primitives and axioms, and the definitions they mention, as data. ACL2 writes it. |
| [`spec/example/`](spec/example) | One theorem and its proof in seven steps, in the formats. |
| [`checks/`](checks) | The checks: scripts and two small books for ACL2, a reader for the formats, the expected results, and `run.sh`, which runs them all. |
| [`LICENSE`](LICENSE) | The licence. |
| [`PLAN.md`](PLAN.md) | The steps of the work, what each gains, and how each is judged finished. |
| [`AGENTS.md`](AGENTS.md) | The rules that bind every change to this repository. |

A reader new to the project should read `spec/language.md`, then sections 1, 5, 6, 9 and 10 of `spec/logic.md`, then `spec/formats.md`.

## Tools

Every tool is found by its name on the `PATH`.

| Tool | Used for |
|---|---|
| `acl2` | ACL2 version 8.6, with the books that are distributed with it, of which `projects/apply/top` must be certified. The checks ask ACL2 what it holds, have it prove the facts that the specification adds to its axioms, and have it certify two small books of their own in `build/`. |
| `python3` | Python 3.5 or later, for `checks/reader.py`, the reader of the formats. |
| `sh`, `cmp`, `cp`, `grep`, `sed`, `tr`, `paste`, `rm`, `mkdir` | The usual POSIX tools, for `checks/run.sh`. |

## The checks

Wherever the specification states something about ACL2, a check confirms it against ACL2 itself. One command runs them all, from the root of the repository:

```
sh checks/run.sh
```

It writes its working files into `build/`, prints one line for each check, and ends with `all checks passed` or `some checks failed`. It was last run on 2026-11-20 with ACL2 8.6, and every line was `ok`.

| Check | What it confirms |
|---|---|
| `checks/ground.lsp` | `spec/ground.txt` is, byte for byte, what ACL2 writes from its own world: its 32 primitive functions and the number of arguments of each; its 84 axioms, four of them as packages; the 122 symbols it refuses as variables; and its definitions of the 36 functions that the ground theory defines, each with the ruler-extenders ACL2 stores. ACL2 proves each of the 41 facts that the specification adds, and a fact that ACL2 did not prove would not be written. |
| `checks/facts.lsp` | `checks/expected/facts.txt` is, byte for byte, what ACL2 says. It holds: ACL2's list of 41 kinds of event; its value for 157 calls of the primitive functions, inside and outside their guards; which names, variables, axioms and packages it refuses; that the rule of the specification for a variable agrees with ACL2's on 3,594 objects; that the walk of the specification records the calls and tests of ACL2's termination machine for all 523 definitions that call themselves in the world ACL2 starts with; ACL2's conjectures for a definition admitted with another well-founded relation, and that the obligations of the specification follow from them; how ACL2 runs an attachment and that it uses none in a proof; how it treats a hidden package; the form of the axiom it stores for a function introduced by choice; the constraint it stores for an `encapsulate`; that it proves the conclusion of every step of the example proof; and counts over the world it starts with. |
| `checks/hidden.lsp`, `checks/outer.lsp` | ACL2 certifies the two small books `checks/hidden.lisp` and `checks/outer.lisp`, copied into `build/`, which give `checks/facts.lsp` a package that ACL2 keeps hidden. |
| `checks/reader.py` | A reader written from `spec/formats.md` reads every file of the repository that is in the format and writes each back unchanged. |
| The counts in `checks/run.sh` | The numbers that the documents give for the ground theory and for the kinds of event are those of the files, every fact of the ground theory is named in `spec/logic.md`, and that document lists the definitions of the ground theory in the order of the file. |

## Licence

Boymoo is published under the MIT No Attribution licence, MIT-0: see [`LICENSE`](LICENSE).
