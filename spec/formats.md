# The interchange formats

This document defines the text that a checker reads and the line that it writes. A checker reads four inputs: the **library**, the **statements** of a book, the **proofs**, and the **library's proofs**. All four, and the ground theory that every checker holds, are written in one small format. A reader for it is a few dozen lines: `checks/reader.py` is one, written from this document, and `sh checks/run.sh` confirms that it reads every file of this repository in the format and writes each back byte for byte (run on 2026-11-26; `all checks passed`). The files `language.md`, `logic.md`, `formats.md` and `ground.txt` are in the directory `spec/`; every other path is given from the root of the repository.

The terms used here are defined in [`language.md`](language.md) (data, symbols, terms, statements) and [`logic.md`](logic.md) (clauses, facts, rules, obligations).

## 1. Files and lines

A file is a sequence of bytes. It is a sequence of **lines**, and each line ends with the byte 10 (a line feed). Every other byte of a file has a value from 32 to 126, so a file is printable ASCII text. There is no comment, no blank line, no tab, and no white space at the end of a line. An empty file has no lines.

A line is

```
(word datum datum ...)
```

an opening parenthesis; a **word**, which is one or more of the lower case letters `a` to `z` and the hyphen; then zero or more data, each preceded by exactly one space; then a closing parenthesis. A word is not a datum: it belongs to the format and says what kind of line this is. No word is in any package, so the format needs no package to exist.

There is exactly one way to write each line. There is no macro, no backquote, no reader conditional, no abbreviation, and no choice of spacing or case.

## 2. The text of a datum

| Datum | Text |
|---|---|
| Integer | `0`; or a digit from `1` to `9` followed by digits; or `-` followed by such a positive number. Never `-0`, never a leading zero. |
| Fraction | An integer other than 0, then `/`, then a positive number greater than 1 with no leading zero. The two have no common factor. |
| Complex rational | `#C(`, a rational (an integer or a fraction), one space, a rational other than 0, `)`. |
| Character | `#\` followed by the two hexadecimal digits of its code, the digits `A` to `F` in upper case. |
| String | `"`, then its characters, then `"`. |
| Symbol | The text of its package name, then `::`, then the text of its name. |
| Cons | `(`, then the text of its elements separated by single spaces, then `)`. If the last `cdr` is not `COMMON-LISP::NIL`, it is written before the closing parenthesis after the three bytes space, `.`, space. |

**Characters inside a string.** A character whose code is from 32 to 126, other than `"` and `\`, is written as itself. Every other character is written as `\` followed by the two hexadecimal digits of its code, in upper case: `\22` for `"`, `\5C` for `\`, `\0A` for a line feed. A character that can be written as itself is never written with `\`.

**The two parts of a symbol.** A **plain** character is an upper case letter `A` to `Z`, a digit, or one of `-+*/<=>!?$%&_^~.@`. A part that is not empty and has only plain characters is written as itself. Any other part is written between two bars, `|`, with its characters written as in a string, except that the bar (`\7C`) is escaped where a string escapes `"`. A part that can be written as itself is never written between bars. So `ACL2::X`, `ACL2::|abc|`, `ACL2::||` and `|My Pkg|::X` are symbols.

**Lists.** The cons whose `car` is `a` and whose `cdr` is the list `(b c)` is written `(a b c)`, never `(a . (b c))`. The empty list is the symbol `COMMON-LISP::NIL` and is written so, never `()`. What follows ` . ` is always an atom other than `COMMON-LISP::NIL`.

**Telling the kinds apart.** The first byte decides: `(` begins a cons, `"` a string, `#` a character or a complex rational, and `|` a symbol. Anything else is a run of plain characters: if `::` follows it, it is the package name of a symbol, and otherwise it must be an integer or a fraction.

Each datum has exactly one text, and each text is the text of one datum. A reader rejects any line that is not the one text of its data.

## 3. Words

| Where | Words |
|---|---|
| The ground theory | `package`, `specials`, `primitive`, `define`, `clause` |
| The library and the statements | `package`, `hidden-package`, `define`, `constrain`, `choose`, `theorem`, `axiom`, `reserve` |
| Program text, for a runner | `define`, `attach` |
| The prover's aids, beside a book | `local`, `hints`, `instructions`, `measure` |
| The proofs and the library's proofs: entries | `define`, `lemma`, `choose`, `theorem`, `measure`, `witness`, `skip` |
| The proofs and the library's proofs: steps | `fact`, `instantiate`, `subsume`, `cut`, `substitute`, `beta`, `compute`, `induct`, `qed` |

A line whose word is not one that may stand where the line stands is rejected.

## 4. Statements

A statement is one line. `language.md`, section 6, says what each kind means, and `logic.md`, section 6, when each is admitted. Here is the exact form of each: the data after the word, in order, with nothing more and nothing less.

| Line | Data |
|---|---|
| `(package NAME IMPORTS)` | `NAME` is a string. `IMPORTS` is a list of symbols. |
| `(hidden-package NAME IMPORTS)` | The same. |
| `(define RULERS D1 ... Dk)` | `RULERS` is the ruler-extenders: the symbol `KEYWORD::ALL`, or a list of symbols. Then one or more definitions. Each `Di` is a list of three elements, `(F FORMALS BODY)`: a symbol, a list of variables, and a term. |
| `(constrain FUNCTIONS FORMULAS)` | `FUNCTIONS` is a list of one or more lists `(F N)`, a symbol and the number of its arguments, an integer that is not negative. `FORMULAS` is a list of zero or more lists `(NAME TERM)`, a symbol and a term. |
| `(choose F BOUND FREE BODY FREE2)` | `F` is a symbol. `BOUND` is a list of one or more variables. `FREE` is a list of variables. `BODY` is a term. `FREE2` is `COMMON-LISP::NIL` or a list of as many variables as `FREE` has. |
| `(theorem NAME TERM)` | `NAME` is a symbol. `TERM` is a term. |
| `(axiom NAME TERM)` | `NAME` is a symbol. `TERM` is a term. |
| `(reserve NAME)` | `NAME` is a symbol. |

For example, ACL2's definition of `not`, as the ground theory holds it, is the line

```
(define COMMON-LISP::NIL (COMMON-LISP::NOT (ACL2::P) (COMMON-LISP::IF ACL2::P (COMMON-LISP::QUOTE COMMON-LISP::NIL) (COMMON-LISP::QUOTE COMMON-LISP::T))))
```

Its ruler-extenders are `NIL`, the empty list: ACL2 stores none for a function that does not call itself, and they are not used.

**The ground theory** is the file [`ground.txt`](ground.txt). It has three words of its own. `(primitive F N)` says that `F` is a primitive function of `N` arguments. `(clause NAME L1 ... Ln)` gives a fact: `NAME` is a symbol or a string, and the `Li` are the literals of its clause, which are terms. `(specials LIST)` gives the symbols of the package `COMMON-LISP` that are never variables (`language.md`, section 5). Its `package` and `define` lines have the form above. No input may contain a `primitive`, a `clause` or a `specials` line.

**Every line costs something to write in full.** A symbol always carries its package, so the line above is 155 bytes with its line feed (`grep -a '^(define COMMON-LISP::NIL (COMMON-LISP::NOT ' spec/ground.txt | wc -c`, 2026-11-20), where ACL2 prints the same body as `(IF P 'NIL 'T)`. What that buys is a reader with no table of packages and no state, one text for each datum, and files that two exporters can compare with `cmp`. `PLAN.md` measures the cost in its second step.

## 5. The four inputs

A checker is a function of four sequences of bytes, given to it apart:

1. **the library**: statements that are taken as given, except those that the fourth input proves;
2. **the statements**: the statements of the book, and of the books it includes, each once and in order;
3. **the proofs**: the proofs of the obligations of the statements;
4. **the library's proofs**: proofs of obligations of statements of the library.

Any of the four may be empty.

**What is given is decided by the first and the fourth input, and by nothing else.** A statement is given exactly when it is a line of the first input that has obligations and the fourth input does not prove it: its entry there is a `skip`, or the fourth input ends before the checker reaches it (section 7). With the fourth input empty, that is every such line of the first. No word, no name, no flag and no position inside the second or third input marks a statement as given or as proved, so a book cannot place its own statements in the library, and a proof of the book's cannot stand for a proof of the library's: whoever runs the checker chooses the first and the fourth input, and the book is the second. The verdict counts what was given, so that a library with more in it than ACL2's own, or with less of it proved, shows in the count.

A statement of the library must be well formed and admissible in every way that needs no proof (`logic.md`, section 6), whether it is given or proved. What is not asked of a given statement is a proof.

**Program text** is no input of a checker. It is what a runner reads (`language.md`, section 4): a file of `define` lines, in the form of the statement, of which a runner uses the definitions and not the ruler-extenders; and of lines `(attach F G)`, two symbols, which say that the runner runs the function `G` in place of the function `F`. `G` is not `COMMON-LISP::IF`, which ACL2 refuses to attach to a function (the line `refused "attach a function to IF"` of `checks/expected/facts.txt`). The program text of a book is read after that of the library, and where two `attach` lines name the same `F`, the later one is in force; so is the later of two `define` lines that define the same function, as where a book moves a function of the library from program mode into logic mode with `verify-termination` and its program text defines the function again. A runner also needs the packages, for `intern-in-package-of-symbol`, `pkg-imports`, `pkg-witness` and `symbol-package-name` (`language.md`, section 3): it takes them from the `package` and `hidden-package` lines of the ground theory, of the library and of the book's statements, and reads no other line of those files.

**The prover's aids** are no input of a checker either. They are what a book gave ACL2's prover and has no logical content (`PLAN.md`, step 2), written beside the book's statements for a prover to use as it sees fit:

| Line | Data |
|---|---|
| `(local BOOK EVENT)` | `BOOK` is a string, the name of a book. `EVENT` is a local event of that book, as its source writes it. |
| `(hints NAME HINTS)` | `NAME` is the name that an event introduced, and `HINTS` the hints that the event gives. |
| `(instructions NAME INSTRUCTIONS)` | The same, for the instructions that an event gives to ACL2's proof builder. |
| `(measure F M REL HOW)` | `F` is a function that calls itself, `M` the measure and `REL` the well-founded relation that ACL2 stores for it, and `HOW` the string `"declared"` if the event that defined `F` declares a measure, and `"default"` if ACL2 chose it. |

## 6. The proofs

The third input is a sequence of **entries**, and so is the fourth. An entry is a head line, and then the proofs that the head calls for. A **proof** is one or more step lines and then the line `(qed)`.

| Head line | What it is for | Proofs that follow |
|---|---|---|
| `(theorem NAME)` | The `theorem` statement named `NAME`. | One, of the clause whose one literal is the theorem's formula. |
| `(measure F M1 ... Mk)` | The `define` statement, or the `define` entry just before it, whose first function is `F` and which has `k` functions. `Mi` is the measure of the `i`-th function, a term. | One for each obligation of termination, in order (`logic.md`, section 6). |
| `(witness F G1 ... Gk)` | The `constrain` statement whose first function is `F`. `Gi` is the function that stands in for its `i`-th function. | One for each formula of the statement, in order. |
| `(skip NAME)` | A `theorem`, `define` or `constrain` statement, or the `define` entry just before it: `NAME` is the theorem's name or the first function's. | None. It is admitted without proof, and the verdict counts it. |
| `(define RULERS D1 ... Dk)` | A definition of the proof's own, in the form of a `define` statement. | None. If some body calls a function of the entry, the next entry is its `measure` or its `skip`. |
| `(lemma NAME L1 ... Ln)` | A fact of the proof's own: the clause of the literals `L1` to `Ln`, one or more terms. `NAME` is a symbol. | One, of that clause. |
| `(choose F BOUND FREE BODY FREE2)` | A function of the proof's own that is introduced by choice, in the form of a `choose` statement. | None. |

A statement **has obligations** if it is a `theorem`, a `define` in which some body calls a function of the same statement, or a `constrain` with at least one formula. A call in the executable half of an `mbe`, `a` in `(return-last 'mbe1-raw a b)`, and a list inside a constant are not calls for this test (`logic.md`, section 6). Every statement of the second input that has obligations has exactly one entry in the third, and the entries stand in the order of the statements. A statement with no obligations has no entry. Before the entry of a statement, the proofs may hold any number of `define`, `lemma` and `choose` entries, which are admitted and checked exactly as they stand, in order. They are how a proof states what a book wrote as local events, and anything else it needs.

**The library's proofs** are read against the library exactly as the proofs are read against the statements, with two differences. A statement of the library whose entry is a `skip` is given: the verdict counts it among the given, not among the skipped. And the library's proofs may end early: a statement of the library that the checker reaches when no line of them remains needs no entry and is given, so an empty fourth input gives every statement of the library that has obligations, and one that stops after the entry of some statement gives all such statements that follow it.

**Steps.** A step line names a rule and gives what the rule takes. The steps of a proof are numbered from 1 in the order they stand, and a premise is the number of an earlier step of the same proof. `logic.md`, section 5, defines the rules.

| Step line | Premises | Other data |
|---|---|---|
| `(fact NAME)` | None. | The name of a fact: a symbol or a string. |
| `(instantiate P S)` | `P` | `S` is a substitution: a list of lists `(V TERM)`, a variable and a term. |
| `(subsume P L1 ... Ln)` | `P` | Zero or more terms, the literals of the conclusion. |
| `(cut P Q)` | `P`, `Q` | None. |
| `(substitute P Q I J1 ... Jk)` | `P`, `Q` | `I` is the number of a literal, from 1. Each `J` is the number of an argument, from 1. |
| `(beta TERM)` | None. | A lambda application. |
| `(compute TERM)` | None. | A call of a primitive function on constants. |
| `(induct P Q PHI M SS)` | `P`, `Q` | `PHI` and `M` are terms. `SS` is a list of substitutions. |

The conclusion of a step is not written: the checker computes it. A proof proves a clause when the conclusion of its last step is exactly that clause: the same literals in the same order. **A proof with no step proves nothing**: a `(qed)` line with no step before it is rejected.

**An example.** [`example/statements.txt`](example/statements.txt) holds one theorem, that every object equals itself, and [`example/proofs.txt`](example/proofs.txt) its proof in seven steps from the facts of the ground theory. `logic.md`, section 8, goes through it.

## 7. The order of checking

A checker does exactly this, and stops at the first line that fails.

1. It starts with the ground theory: its packages, functions and facts.
2. It takes the lines of the library in order. Each must be a line of the format, every symbol on it must exist (`language.md`, section 2), and it must be a statement that meets every condition of its kind except the obligations (`logic.md`, sections 6 and 7). If the statement has obligations and no line of the library's proofs remains, the statement is **given**. If it has obligations and a line remains, the checker reads the library's proofs from where it stopped (bytes that remain with no line feed after them are a line, which fails when it is read):
   - while the next head line is a `define`, a `lemma` or a `choose`, it admits or checks that entry;
   - the next head line must then be the entry of this statement: `theorem`, `measure`, `witness` or `skip`, with this statement's name. With a `skip` the statement is **given**. With one of the others the checker checks the proofs of that entry, and the statement is **proved**.
3. When the library is done, its proofs must be done too. Nothing is read from the proofs until then.
4. It takes the lines of the statements in order. Each must pass the same tests as a line of the library, with the one more that a book may not define a function whose name is a symbol of `COMMON-LISP` (`language.md`, section 6). If the statement has obligations, the checker then reads the proofs from where it stopped:
   - while the next head line is a `define`, a `lemma` or a `choose`, it admits or checks that entry;
   - the next head line must then be the entry of this statement: `theorem`, `measure`, `witness` or `skip`, with this statement's name. It checks the proofs of that entry.
5. When the statements are done, the proofs must be done too.

A line of the library or of the statements that is, byte for byte, an earlier line of either is not tested again: it is admitted, adds nothing and takes no entry (`language.md`, section 6).

A line **fails** when it is not a line of the format, when a symbol on it does not exist, when its word may not stand there, when it does not have the data of its kind, when a condition of `logic.md` on it does not hold, or when a budget of section 8 is passed. A `(qed)` line fails when the proof it ends has no step or does not prove its clause. When the proofs end before a statement of the second input with obligations has everything it calls for, the statement's line fails. That is so wherever they end: before the head line of the statement's entry; after `define`, `lemma` or `choose` entries that stand before it; inside a proof, after its head or after some of its steps; between the proofs of one entry; or after a `define` entry that still waits for its `measure` or `skip`. No line of the proofs fails because the proofs end. When the statements are done and a line of the proofs remains, that line fails.

All of this holds of the library's proofs and the statements of the library, with one difference: a statement of the library that the checker reaches when no line of the library's proofs remains is given, and no line fails. If a line remains then, and the library's proofs end before the statement has everything it calls for, the statement's line fails, wherever they end: after `define`, `lemma` or `choose` entries that stand before its entry, inside a proof, between the proofs of one entry, or after a `define` entry that still waits for its `measure` or `skip`. When the library is done and a line of its proofs remains, that line fails.

Each test of a line uses only the lines that the order above puts before it, so the first line that fails is the same for every checker, whether it reads each input whole before it starts or one line at a time.

## 8. Budgets

Every check is bounded, so that no input makes a checker run without end. The bounds are stated in sizes, not in time, so that two checkers reject the same lines.

The **size** of a datum is 1 for an atom, and for a cons 1 more than the sizes of its `car` and its `cdr` together. The size of a clause is the sum of the sizes of its literals.

| Budget | Bound | The line that fails |
|---|---|---|
| The conclusions of the steps of one proof | Their sizes sum to at most 2<sup>26</sup> (67,108,864). | The step whose conclusion passes the bound. |
| The obligations of termination of one `define` | Their sizes sum to at most 2<sup>26</sup>. A clause that is left out because it is the same as an earlier one (`logic.md`, section 6) does not count. | Its `measure` line. A `skip` is not affected: it asks for no obligation. |

**Why these two are enough.** Reading a line takes time bounded by a polynomial in its length: in proportion to its length, except for its numbers, whose values a reader computes from their digits and, for a fraction, confirms to be in lowest terms. The conclusion of a `fact` step is a clause that an earlier line stated or an earlier proof concluded. The conclusions of `subsume`, `cut`, `substitute` and `induct` are no larger than their premises and the data of their own lines together. `compute` takes its arguments from its own line, and the value of a primitive is found in time bounded by a polynomial in the length of that line, or is the list of imports that an earlier line gave. The conclusions of `instantiate` and `beta` are no larger than the product of two such sizes. Without a bound, a chain of `instantiate` steps could square a size at every step; the first budget stops that, and bounds the work of every comparison, since each compares conclusions or data of a line. The obligations of a definition are built by substitution through nested lambdas, which can double a size at every level; the second budget stops that. A checker must find the size of what it is about to build without building it, which the sizes of the parts allow. To leave out a clause of termination that is the same as an earlier one, a checker compares it with the clauses it keeps; only a clause whose size is that of a clause kept can be the same, and that size is within the budget.

Within the budgets a check can still be slow: a `subsume` step compares each literal of its premise with each literal on its line. The bounds make every check end; they do not make it fast.

## 9. The verdict

A checker writes one line, ended by a line feed. It is one of three.

```
accepted
provisional skipped S assumed A given-definitions D given-facts F
rejected INPUT N
```

- **`accepted`**: every line was admitted, every obligation was proved, and all four counts below are 0.
- **`provisional ...`**: every line was admitted and every proof given was checked, and at least one count is not 0. Each count is written in decimal with no leading zero.
  - `S`, **skipped**: the entries `(skip NAME)` in the proofs, and those in the library's proofs that follow a `define` entry and are for it.
  - `A`, **assumed**: the `axiom` statements among the statements.
  - `D`, **given definitions**: the statements of the library that are given and are a `define` or a `constrain`. Their termination, or their witness, was not shown.
  - `F`, **given facts**: the `theorem` statements of the library that are given, and the `axiom` statements of the library.
- **`rejected INPUT N`**: `INPUT` is `library`, `statements`, `proofs` or `library-proofs`, and `N` is the number, counted from 1 and written in decimal, of the first line of that input that fails, in the order of section 7. The place is the name of what failed: a line holds one statement, one head or one step.

Nothing is accepted by default. A statement of the second input with obligations and no entry is a rejection; a proof with no step is a rejection; a skipped proof, an assumed axiom and a given statement each add to a count, and any count that is not 0 makes the verdict provisional.

A checker may write more lines after the first, to say what it found. They are not specified, and nothing may be concluded from them.
