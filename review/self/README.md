# Termination proofs for the checker

Run from the repository root.

```sh
sh review/self/run.sh
```

On 2026-11-24 this command gave `accepted` on the JavaScript checker
and on the reference runner, with an empty library. The 241 statements
include 210 definitions and 102 entries with termination obligations.
The generated source proofs cover all 102 entries, with zero skips.

The script builds the checker with `checker/build.sh` and the runner
with `runner/Makefile`. It supplies the exporter with the names of the
37 ground definitions in `build/export/ground-fns.lsp`. The generator
uses the exported statements and the clauses and definitions of
`spec/ground.txt`. It writes the source and logical-body checks to
`build/self/` and passes each input to both checkers. [run.sh](run.sh)

## Writing proofs

Each recipe builds a conclusion from other steps. The derived
operations open definitions, select branches of `if`, extract
conjuncts, apply implications and join cases. A recipe can reason
under a test `P` by using the proved clause containing `P` and
`(not P)`. The latter stays as a side literal until discharged by
a cut or included in the final clause. The writer numbers the steps
used by the last conclusion, shares identical steps within one proof
and emits only the eight rules of `spec/logic.md`, section 5.
[proof.py](proof.py)

The termination walk carries substitutions through lambda bodies
and records the signed tests specified by the ruler-extenders.
The generator visits definitions in statement order. It uses the
same ordered clauses for proof generation and for the logical-body
comparison. It makes a prior definition's equation available after
generating the proofs that admit the definition.
[termination.py](termination.py), [pilot.py](pilot.py)

Most measures are `acl2-count` of one formal per function. The
generator matches the first literal of a built-in clause to the
obligation and checks that the clause's side literals are available.
For example, a call on `(cdr x)` under `(consp x)` takes a `fact`
step for `"built-in-clause-3"`, an `instantiate` step for `x`,
and a `subsume` step to put the ruler literals in order.
`"built-in-clause-1"` gives ordinality. The same matching applies to
the countdowns, using the clauses for subtracting one under the
appropriate test. [descent.py](descent.py)

## Lemmas and other measures

- The equality and propositional lemmas implement conditional rewriting
  and case analysis. The arithmetic lemmas derive integer closure,
  sign and order rules, and natural number ordinality. They use
  reassociation, commutation and cancellation of additive inverses to
  identify equal integer sums. `o<` agrees with `<` on integers.
- `acl2-count` is numeric by its definition and natural because it
  is an ordinal and a number. The prelude proves `len` natural by
  induction on `acl2-count`, using the ground `cdr` clause. The
  weak selector bounds allow a chain of selectors to pass through an
  atom. A strict first edge and weak later edges still give a
  strict decrease.
- `TENS-UP-TO`, `DIGIT-COUNT` and `SIXTEENS` measure a gap between
  an upper and lower endpoint. The proof defines `ACL2::SELF-NFIX`
  to return its argument when natural and zero otherwise.
  `ACL2::SELF-GAP` clips a difference this way. With a positive
  initial gap, increasing the lower endpoint decreases the measure.
  The lower endpoint grows by tenfold multiplication for
  `TENS-UP-TO` and by one for the other two.
- The four functions of `WALK` use `acl2-count` plus one for
  walking and `acl2-count` for recording. A walk can hand the same
  term to the recorder, which drops the added one. Every other
  call descends through selectors and the phase stays the same or
  decreases. `RUN` uses the sum of the lengths of the two input
  line lists because each call removes a line from one of them.
- `PARSE-LOOP` measures the length of the characters left to
  read. Its lexer lemmas describe the suffix carried in a result.
  The plain scan never lengthens the suffix and shortens it
  when it consumes a first character. Induction on the input
  count proves the plain and quoted scan bounds. The other
  lexer proofs split the translated return expressions into
  branches and compose the bounds for the calls in each
  successful branch. The atom lemma then handles both recursive
  calls in `PARSE-LOOP` that use lexer results. The dotted-tail
  branch also takes cdrs of the input and of the lexer result.

[library.py](library.py), [lexer.py](lexer.py)

## Logical-body comparison

The 13 functions containing `mbe` are listed in `build/self/mbe.tsv`.
The run constructs a statement file in which each `mbe` is replaced
by its logical half and checks the proofs for that file with both
checkers. On 2026-11-24 both gave `accepted`. For each affected
statement the two walks gave the same ordered obligations after
erasing nested `mbe` wrappers in clause terms.

Twelve clauses differ in their exact text before that erasure.
The entries of `CALLS-P`, `RENAME-CALLS` and `WALK` account for
three, one and eight of these clauses, respectively. In eleven of
the clauses the wrapper is in an argument of the measure comparison.
In the remaining clause it is in a ruler test of `CALLS-P`.
Section 6 of `spec/logic.md` skips the executable half during
the walk. The terms copied from recorded arguments and tests retain
their wrappers. Proofs of the exported statements cite the equation
of `return-last` wherever a comparison needs the logical argument.

The exact clauses can also be checked by passing the logical-body
proofs with the exported statements. On 2026-11-24 both commands
below gave `rejected proofs 6018` at the first differing `qed`.

```sh
sh checker-js/check.sh build/self/empty build/checker/checker.statements build/self/logical.proofs node
sh checker/check.sh build/self/empty build/checker/checker.statements build/self/logical.proofs
```

## Measurements

These are from `sh review/self/run.sh` on 2026-11-24.
`build/self/sizes.tsv` gives the number of steps in each obligation
and the step total and byte size of each source entry, lemma and
definition in the proofs. Entry bytes include the head and `qed`
lines. Step counts count only rule applications.

| Entries in the source proof file | Entries | Steps | Bytes |
|---|---:|---:|---:|
| Source measures and their 262 obligations | 102 | 3,182 | 795,721 |
| Lemmas | 60 | 4,645 | 2,001,229 |
| Definitions in the proofs | 2 | 0 | 252 |
| Whole proof file | 164 | 7,827 | 2,797,202 |

The source proof file has 8,313 lines. Of the 262 source obligations,
223 take two or three steps, and 81 source entries take five steps
in total. The seven lexer lemmas account for 2,094 steps and
1,683,286 bytes. Their proofs carry the translated branch terms
through case splits and substitutions.

| Source entry | Proofs | Steps | Bytes |
|---|---:|---:|---:|
| `TENS-UP-TO` | 2 | 106 | 30,758 |
| `DIGIT-COUNT` | 2 | 70 | 23,261 |
| `SIXTEENS` | 2 | 70 | 17,689 |
| `PARSE-LOOP` | 6 | 276 | 101,765 |
| `WALK` | 22 | 1,322 | 398,744 |
| `RUN` | 3 | 108 | 18,462 |

The timing files record elapsed wall time after export and compilation,
including the checker wrappers and the whole input.

| Input | JavaScript | Reference runner |
|---|---:|---:|
| Source | 0.48 s | 4.38 s |
| Logical bodies | 0.36 s | 3.86 s |
