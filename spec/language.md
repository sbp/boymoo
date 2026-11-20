# The language

This document defines the language that Boymoo checks, which this repository calls **ACL2 Core**. ACL2 Core is what remains of an ACL2 book once ACL2 has expanded every macro: data, the 32 primitive functions, terms, and eight kinds of statement. ACL2's documentation names the parts, "translated terms" (its topic TERM) and "primitive event macros" (the comment before `primitive-event-macros` in its source file `translate.lisp`); the name ACL2 Core for the whole is this project's.

**ACL2 is the definition of ACL2.** Wherever ACL2 decides something, by its axioms, by its evaluator or by the tests it makes before it admits an event, ACL2 Core decides the same, and a check confirms it against ACL2. `EDGE-CASES.md`, at the root of the repository, lists every place where what ACL2 does goes beyond, falls short of or differs from what its axioms say, what ACL2 Core does there, and the places where ACL2 Core cannot follow. [`logic.md`](logic.md) gives the axioms and the rules of proof, and [`formats.md`](formats.md) gives the text in which statements and proofs are written.

Statements about ACL2 in this document are confirmed against ACL2 8.6 by `sh checks/run.sh`, run from the root of the repository. It was last run on 2026-11-20 and printed `all checks passed`. `README.md` says what each check covers. The files `language.md`, `logic.md`, `formats.md` and `ground.txt` are in the directory `spec/`; every other path is given from the root of the repository.

## 1. Data

A **datum** is one of the following objects. They are the objects that ACL2 can read and print.

| Kind | What it is | Written (see `formats.md`, section 2) |
|---|---|---|
| Integer | A whole number of any size. | `0`, `17`, `-3` |
| Fraction | A rational number that is not an integer. | `3/4`, `-1/3` |
| Complex rational | A complex number whose real and imaginary parts are rational and whose imaginary part is not 0. | `#C(1 2)`, `#C(1/2 -1)` |
| Character | One of 256 characters, each with a code from 0 to 255. | `#\41` |
| String | A finite sequence of characters. | `"abc"` |
| Symbol | An object with a name and the name of a package, both strings (section 2). | `ACL2::X`, `COMMON-LISP::CAR` |
| Cons | A pair of two data, its `car` and its `cdr`. | `(1 . 2)`, `(1 2 3)` |

The integers and the fractions together are the **rationals**. The rationals and the complex rationals together are the **numbers**. A datum that is not a cons is an **atom**. Two data are the same object exactly when they are of the same kind and have the same parts, so every datum has exactly one text.

**The universe is not closed.** The axioms never say that every object is a datum. ACL2's logic allows objects that are none of the kinds above, which ACL2 calls bad atoms, and the axioms of `logic.md` hold of them too. No statement and no proof can write one.

## 2. Symbols and packages

A symbol has a **name** and a **package name**, which the primitives `symbol-name` and `symbol-package-name` give. Two symbols with the same name and the same package name are the same symbol. The text `PKG::NAME` denotes the symbol whose package name is `PKG` and whose name is `NAME`. There is no other way to write a symbol, so the text of a symbol never depends on what any package imports.

A **package** has a name, which is a string that is not empty, and a list of symbols that it **imports**. A name that a package imports is, in that package, the imported symbol, which belongs to another package. So a package has no symbol of its own with the name of one of its imports. ACL2's package `ACL2` imports `COMMON-LISP::CAR`, and therefore no object is `ACL2::CAR`.

**The rule of existence.** The symbol `PKG::NAME` exists exactly when both of these hold:

1. a package named `PKG` has been declared, by the ground theory (`logic.md`, section 3) or by a `package` or `hidden-package` statement that stands earlier in the input;
2. no symbol that `PKG` imports has the name `NAME`.

**A checker rejects every line that writes a symbol that does not exist.** The rule applies to every symbol on every line of every input: in a term, in a quoted constant, as a name of a function, a variable, a theorem or a lemma, in a statement and in a proof. `logic.md`, section 9, shows why soundness needs the rule and why the rule is enough whoever wrote the statements.

## 3. The primitive functions

ACL2 has 32 primitive functions: functions with no definition, whose meaning is given by axioms. The table gives the number of arguments of each and its value on every tuple of data, including the data outside the guard that ACL2 gives it. A **guard** is a condition that ACL2 asks of the arguments before it runs a function; it is no part of the logic, and ACL2 Core has no guards. In the table, "fixed" means that an argument that is not a number is taken as 0.

| Function | Arguments | Value |
|---|---|---|
| `acl2-numberp x` | 1 | `T` if `x` is a number, otherwise `NIL`. |
| `bad-atom<= x y` | 2 | `NIL` on any two data (section 4). |
| `binary-* x y` | 2 | The product of `x` and `y`, both fixed. |
| `binary-+ x y` | 2 | The sum of `x` and `y`, both fixed. |
| `unary-- x` | 1 | The negative of `x`, fixed. |
| `unary-/ x` | 1 | The reciprocal of `x` if `x` is a number other than 0, otherwise 0. |
| `< x y` | 2 | With both fixed: `T` if the real part of `x` is less than that of `y`, or the real parts are equal and the imaginary part of `x` is less than that of `y`; otherwise `NIL`. |
| `car x` | 1 | The `car` of `x` if `x` is a cons, otherwise `NIL`. |
| `cdr x` | 1 | The `cdr` of `x` if `x` is a cons, otherwise `NIL`. |
| `char-code x` | 1 | The code of `x` if `x` is a character, otherwise 0. |
| `characterp x` | 1 | `T` if `x` is a character, otherwise `NIL`. |
| `code-char x` | 1 | The character with code `x` if `x` is an integer from 0 to 255, otherwise the character with code 0. |
| `complex x y` | 2 | The number `x + iy`, where an argument that is not rational is taken as 0. It is a rational when the second is 0. |
| `complex-rationalp x` | 1 | `T` if `x` is a complex rational, otherwise `NIL`. |
| `coerce x y` | 2 | If `y` is the symbol `COMMON-LISP::LIST`: the list of the characters of `x` if `x` is a string, otherwise `NIL`. If `y` is anything else: the string made from `x` read as a list, which has one character for the `car` of `x` and of each `cdr` of `x` that is a cons, that `car` itself if it is a character and otherwise the character with code 0. |
| `cons x y` | 2 | The cons whose `car` is `x` and whose `cdr` is `y`. |
| `consp x` | 1 | `T` if `x` is a cons, otherwise `NIL`. |
| `denominator x` | 1 | The denominator of `x` in lowest terms, which is positive, if `x` is rational; otherwise 1. |
| `equal x y` | 2 | `T` if `x` and `y` are the same object, otherwise `NIL`. |
| `if x y z` | 3 | `z` if `x` is `NIL`, otherwise `y`. |
| `imagpart x` | 1 | The imaginary part of `x` if `x` is a number, which is 0 for a rational; otherwise 0. |
| `integerp x` | 1 | `T` if `x` is an integer, otherwise `NIL`. |
| `intern-in-package-of-symbol x y` | 2 | If `x` is a string and `y` is a symbol, whose package is `P`: the symbol named `x` that `P` imports, if it imports one, and otherwise the symbol of `P` named `x`; this holds also when `P` is a hidden package, whose imports are those its statement declares. If `x` is not a string or `y` is not a symbol: `NIL`. |
| `numerator x` | 1 | The numerator of `x` in lowest terms if `x` is rational, otherwise 0. |
| `pkg-imports x` | 1 | If `x` is the name of a package declared by a `package` statement or by the ground theory: the list of its imports, in the order of its declaration. If `x` is not a string: `NIL`. For any other string: not computed (section 4). |
| `pkg-witness x` | 1 | If `x` is the name of a package declared by a `package` statement or by the ground theory: the symbol of that package named `ACL2-PKG-WITNESS`. If `x` is not a string: `ACL2::ACL2-PKG-WITNESS`. For any other string, the empty string among them: not computed (section 4). |
| `rationalp x` | 1 | `T` if `x` is rational, otherwise `NIL`. |
| `realpart x` | 1 | The real part of `x` if `x` is a number, otherwise 0. |
| `stringp x` | 1 | `T` if `x` is a string, otherwise `NIL`. |
| `symbol-name x` | 1 | The name of `x` if `x` is a symbol, otherwise the empty string. |
| `symbol-package-name x` | 1 | The package name of `x` if `x` is a symbol, otherwise the empty string. If `x` is a symbol of a hidden package: not computed (section 4). |
| `symbolp x` | 1 | `T` if `x` is a symbol, otherwise `NIL`. |

Here `T` and `NIL` are the symbols `COMMON-LISP::T` and `COMMON-LISP::NIL`. The ground theory declares the packages `COMMON-LISP`, `KEYWORD`, `ACL2`, `ACL2-INPUT-CHANNEL` and `ACL2-OUTPUT-CHANNEL`, so the symbols of this table exist in every input.

**Checked against ACL2.** The 32 names and the number of arguments of each are the lines `(primitive NAME N)` of [`ground.txt`](ground.txt), which the check writes from ACL2's own list, `*primitive-formals-and-guards*`. The values are confirmed on 157 calls, at least two for each primitive and at least one outside each guard: the lines `(value TERM V)` of `checks/expected/facts.txt` are ACL2's values with guard checking off, and the lines `(no-value TERM)` are the calls ACL2 refuses to evaluate.

**The table is ACL2's evaluator.** On every one of the 157 calls the table gives the value that ACL2 gives, and gives none where ACL2 gives none.

## 4. Computing

To **compute** a call of a primitive on data is to find its value by the table of section 3. A checker computes what ACL2's evaluator computes, and refuses what it refuses. Three kinds of call are refused, and a proof that asks for one is rejected:

| Call | What ACL2 does |
|---|---|
| `pkg-imports` on a string that names no package, or names a hidden one | ACL2 refuses to evaluate it: the argument "is not the name of a package currently known to ACL2". |
| `pkg-witness` on a string that names no package, or names a hidden one | The same. The empty string names no package. |
| `symbol-package-name` on a symbol of a hidden package | ACL2 refuses to evaluate it: the symbol "is not in any of the packages known to ACL2" (`EDGE-CASES.md`, entry 2.9). |

A **hidden** package is one that a `hidden-package` statement declares (section 6). `intern-in-package-of-symbol` at a symbol of a hidden package is computed, from the imports that its statement declares, because ACL2's evaluator computes it and ACL2 proves theorems by it (`EDGE-CASES.md`, entry 1.3). Facts about the refused calls come only from the axioms. For `(pkg-witness "")` the axioms do give facts: `symbol-package-name-pkg-witness-name` says that its package name is `"ACL2"`, and the check has ACL2 prove that from the axiom, although ACL2 will not evaluate the call.

**Where ACL2 computes and no axiom speaks.** ACL2's evaluator gives `NIL` for `bad-atom<=` on any two data, and ACL2 proves theorems by that evaluation: the check has it prove `(equal (bad-atom<= 1 2) nil)`. None of its axioms says so; they order only the objects that are not data. ACL2 Core computes `NIL` too.

Every call of a primitive on data that is computed has a value that is a datum whose symbols exist (`logic.md`, section 9).

A checker never computes a call of a function that is not primitive. The value of a defined function on data is reached in a proof by its definition and the rules, step by step. Running a program fast is the work of the runner and the compiler of `PLAN.md`, which prove nothing.

### Running

A **runner** computes the value of a term with no variables. It is given **program text**: `define` lines, and `attach` lines (`formats.md`, section 5). The value is defined by the table of section 3 and the definitions:

- the value of `(quote c)` is `c`;
- the value of a call of a primitive is the table's value on the values of its arguments, and where the table gives none the runner stops, as ACL2 does;
- the value of a call of a defined function is the value of its body with the formals bound to the values of the arguments;
- the value of a lambda application is the value of its body with its formals bound to the values of its actuals;
- the value of `(if a b c)` is the value of `c` if the value of `a` is `NIL`, and otherwise the value of `b`; the branch not taken is not evaluated;
- the second argument of `(return-last 'mbe1-raw x y)` is not evaluated. It is the executable half of an `mbe`, whose recursive calls ACL2 does not measure (`logic.md`, section 6).

**Attachments.** A line `(attach F G)` of the program text says that the runner runs `G` in place of `F`: the value of a call of `F` is the value of the call of `G` on the same arguments. `F` is a function with no definition, introduced by a `constrain` statement, and `G` is a function with as many arguments. This is ACL2's `defattach`, as ACL2 uses it when it runs a term at its top level. An attachment is no part of the logic: no statement holds one, a checker never reads one, and ACL2 itself uses none when it evaluates a term in a proof or for a constant. The check records all three.

**A function with no definition and no attachment has no value,** and the runner stops, as ACL2 does. Such are the functions of a `constrain` or a `choose` statement, and any function for which the runner was given no program text (section 7).

**Where a runner stops as ACL2 does.** The value these rules give is ACL2's value with guard checking `:none` (`EDGE-CASES.md`, entries 2.4 and 10.2). ACL2 gives no value for a call of `hard-error` or of `throw-nonexec-error`, although each is defined to be `NIL`, and through them `illegal`, `er hard` and every function that is not executable stop too. So the program text holds no definition for these two functions, and a runner stops at a call of either (entries 2.2 and 2.3). In a function whose guards are verified ACL2 runs the executable half of an `mbe`, and a runner the other half; verifying the guards proves the two equal wherever ACL2 runs the executable one, so they differ only where it gives no value (entry 2.5).

**Every run ends.** When the obligations of termination of every definition have been proved, the computation of a value by these rules ends: each recursive call that the rules evaluate is one that ACL2's termination machine measures, under tests that hold when the call is reached (`logic.md`, section 6).

## 5. Terms

A **term** is a datum of one of four shapes. These are ACL2's translated terms, the form in which ACL2 holds a formula after it has expanded every macro.

| Shape | Form | Conditions |
|---|---|---|
| Variable | a symbol | It is not `COMMON-LISP::T`, not `COMMON-LISP::NIL`, and not a symbol of the package `KEYWORD`. |
| Constant | `(COMMON-LISP::QUOTE c)` | A list of exactly two elements; `c` is any datum. |
| Call | `(f a1 ... an)` | `f` is a symbol that names a function in use, `n` is its number of arguments, and each `ai` is a term. |
| Lambda application | `((COMMON-LISP::LAMBDA (v1 ... vn) body) a1 ... an)` | The `vi` are distinct variables, `body` is a term whose variables are all among the `vi`, there are exactly as many actuals `ai` as formals `vi`, and each `ai` is a term. |

Every list is a true list: its last `cdr` is `NIL`. A function is **in use** from the line that introduces it: the primitives and the definitions of the ground theory from the start, and every other function from its statement or from the definition in the proof that introduces it. A checker confirms that every term it is given, in a statement or in a proof, is a term in this sense.

**Variables.** A symbol is a variable exactly when ACL2 accepts it as one. Let `P` be its package name and `N` its name. It is a variable when all of these hold:

1. it is not `COMMON-LISP::T` and not `COMMON-LISP::NIL`;
2. `P` is not `KEYWORD`;
3. `N` does not both begin and end with the character `*`. A name that is the one character `*` does both;
4. `N` does not begin with the character `&`;
5. if `P` is `COMMON-LISP`, the symbol is one that the package `ACL2` imports, and is not one of the 122 symbols on the `specials` line of the ground theory, which are the names that Common Lisp holds as special variables and constants.

So `ACL2::X`, `COMMON-LISP::LIST` and the symbol with the empty name `ACL2::||` are variables; `ACL2::*X*`, `ACL2::&X`, `COMMON-LISP::PI` and every keyword are not. Formals, the variables of a lambda, and the variables of a substitution are variables in this sense, and where several stand together they are distinct.

**`COMMON-LISP::QUOTE` is never the name of a function.** A list that begins with it is a constant. If a function could have that name, a call of it would be read as a constant, and a fact proved of the call would be stated of the constant. Section 6 gives the rest of ACL2's rules for names.

**Checked against ACL2.** The rule for a variable, computed from the two lists of the ground theory, agrees with ACL2's own test `legal-variablep` on 3,594 objects: every import of `ACL2`, every symbol of the `specials` line, every formal of every function ACL2 starts with, and symbols chosen to try each clause. This is a line `agrees` of `checks/expected/facts.txt`. The lines `refused` and `accepted` of that file record ACL2's answer to a definition with each kind of formal.

**Substitution.** A substitution is a list of pairs of a variable and a term, with distinct variables. To apply it to a term is to replace every occurrence of each variable by its term, all at once. It replaces nothing inside a constant, and nothing inside the body of a lambda, whose variables are all bound; it does replace inside the actuals of a lambda application. Because the body of every lambda is closed, no variable is ever captured.

## 6. Statements

A book is given to a checker as a list of **statements**, in the book's order: one for each event that has logical content, and one for each name that an event with none takes. There are eight kinds. `formats.md`, section 4, gives the exact text of each, and `logic.md`, section 6, gives the conditions under which each is admitted and what must be proved.

| Statement | What it says | What it adds to the logic |
|---|---|---|
| `package` | A package has this name and imports exactly these symbols, in this order. | The axiom `(equal (pkg-imports "NAME") '(imports))`. |
| `hidden-package` | A package has this name and these imports, and ACL2 keeps it hidden. | Nothing. The symbols of the package can be written; its imports are not computed and no fact gives them. |
| `define` | One function, or several that may call one another, each with formals and a body, and the ruler-extenders under which ACL2 admitted them. | For each function, the equation `(equal (f x1 ... xn) body)`. |
| `constrain` | One or more functions with no definition, and named formulas about them. | Each formula, as a fact under its name. |
| `choose` | A function that gives values for some variables that make a formula true, if any values do. | One axiom, which the checker builds from the statement. |
| `theorem` | A named formula that follows from what stands before it. | Nothing new: the formula becomes a fact that later proofs may cite. |
| `axiom` | A named formula taken without proof. | The formula. It always shows in the verdict. |
| `reserve` | A name is in use for something with no logical content. | Nothing. |

### Names

A **name** is in use from the line that introduces it, and no line may introduce a name that is in use. The names are those of functions, of theorems, of axioms, of the formulas of a `constrain` statement, of the lemmas of a proof, and those that a `reserve` statement holds. They share one space, as in ACL2, where one symbol cannot name both a function and a theorem. These are ACL2's rules, and ACL2 Core has no others. ACL2 also refuses a name that the Lisp under it defines, and any event that calls a function it holds untouchable; ACL2 Core does neither, and no statement that ACL2 writes is affected (`EDGE-CASES.md`, entry 6.1).

- **Every name is a symbol that is not a keyword.**
- **A function name is not `COMMON-LISP::QUOTE`,** as section 5 says.
- **In the statements of a book and in the proofs, a function name is not a symbol of the package `COMMON-LISP`.** ACL2 defines functions of that package, such as `not` and `length`, only while it builds itself; the ground theory and the library are that building, and there such names stand. A theorem may be named by a symbol of `COMMON-LISP`.
- **The names of the ground theory are in use from the start:** its functions, its facts, and `COMMON-LISP::T` and `COMMON-LISP::NIL`, which ACL2 holds as constants.
- **A `package` statement takes the name of its rule.** ACL2 keeps the axiom of the package `NAME` as a rule called `NAME-PACKAGE`. The statement brings into use the symbol that this string names in the package `ACL2`, which is the value of `(intern-in-package-of-symbol "NAME-PACKAGE" 'ACL2::X)`, and its fact has that name (`logic.md`, section 4).
- **A `reserve` statement holds a name** under which ACL2 has something with no logical content: a macro, a constant, a label, a theory, a single-threaded object. No later line may take it.

**A line that repeats an earlier one adds nothing.** ACL2 accepts an event that repeats one it has, and does nothing. A line of the library or of the statements that is, byte for byte, an earlier line of either is admitted, adds nothing, and takes no entry in the proofs.

**Checked against ACL2.** The lines `refused` and `accepted` of `checks/expected/facts.txt` record that ACL2 refuses a function named by a keyword or by a symbol of `COMMON-LISP`, and a theorem named by a keyword, by `T`, by `NIL`, by the name of a function, or by the name of the rule of a package; that it refuses a function with the name of a macro or of a constant; that it accepts a function named `*BM*` or `&BM` and a theorem named by a symbol of `COMMON-LISP`; and that it accepts a repeated theorem or definition and refuses the same name with other content. ACL2 8.6 starts with 94 functions in logic mode whose names are symbols of `COMMON-LISP` (a line `count`).

## 7. The events of ACL2

ACL2 builds its logical world from **events**. Every event of a book, once its macros are expanded, is a call of one of the event forms that ACL2 lists in its function `primitive-event-macros`, or is `defpkg`, which ACL2 allows only in the commands that stand before a book. The list has 41 members in ACL2 8.6: the lines `(event NAME)` of `checks/expected/facts.txt` are that list as ACL2 gives it.

The table says, for each, whether it has **logical content**, which means that it adds a function or a formula to the theory, and what it becomes in ACL2 Core. An event with no logical content becomes no statement, or only a `reserve` statement for the name it takes.

| Event | Logical content | In ACL2 Core |
|---|---|---|
| `defun` in logic mode | Yes: the equation of the function. | `define` with one function. The body is the term ACL2 stores as the body of the definition, in which `mbe`, `prog2$`, `ec-call` and their relatives stand as calls of the function `return-last`. The statement also carries the ruler-extenders under which ACL2 admitted the definition, because they decide what must be proved of it. The measure, the well-founded relation, the guard and the other declarations are no part of the statement (`logic.md`, section 6). |
| `defuns`, `mutual-recursion` in logic mode | Yes: one equation for each function. | `define` with several functions. |
| `defun` in program mode | No. ACL2 can run the function and proves nothing of it. | No statement. As a program, it is written with the text of a `define` in a file that only a runner reads, where ACL2 has a definition for it in its own language (see below). |
| `verify-termination-boot-strap` | Yes, when it moves a function into logic mode: its equation. | `define`. |
| `defthm` | Yes, as an obligation: the formula must follow. | `theorem`. Its rule classes and hints only guide ACL2's prover. A theorem that ACL2 keeps as a rule of the class `:well-founded-relation` is a `theorem` like any other. |
| `defaxiom` | Yes: the formula. | `axiom`. ACL2 allows it only at the top level of a book: not inside `local` and not inside `encapsulate`. |
| `defchoose` | Yes: the axiom of choice for one formula. | `choose`. |
| `encapsulate` with a signature | Yes: the functions of the signature, with the constraint ACL2 stores for them. | `constrain`, then a statement for each event inside it that is not local and is not part of the constraint. The functions of the `constrain` statement are those of the signature and every function defined inside whose equation ACL2 puts into the constraint, which it marks by holding the name of a function of the signature as that function's constraint: for example one whose recursion a function of the signature rules, or one that an exported theorem mentions together with such a function (`EDGE-CASES.md`, entry 6.6). Its formulas are the constraint, which ACL2 stores on one of the functions while the others hold that function's name (entry 6.7). `defun-sk` is such an `encapsulate` (entry 6.9). The local definitions, which are the witnesses, become no statement: they belong to the proof (`logic.md`, section 6). |
| `encapsulate` with no signature, `progn`, `progn!` | Only that of the events inside. | The statements of those events. `progn!` can also change ACL2 itself under a trust tag, which no statement expresses. |
| `defstobj` | Yes: the definitions of the recognizers, the creator, and the functions that read and write the fields of a single-threaded object. | One `define` for each, and a `reserve` for the name of the object. That an object is single-threaded is a rule about how programs may use it, and has no logical content. |
| `defabsstobj` | Yes: each exported function, defined as a call of its logical function. | One `define` for each. The correspondence theorems it asks for concern execution only. |
| `defpkg` | Yes: the imports of the package. | `package`. A package that ACL2 keeps only because a book included locally declared it becomes `hidden-package`. |
| `include-book` | That of the included book's events that are not local. | No statement of its own. The statements of the included book stand before those of the book, each book once. |
| `defconst` | No, once terms are translated: ACL2 puts the constant's value, quoted, wherever a term names it. | `reserve`, for its name. |
| `defmacro` | No: a macro is expanded before a term exists. | `reserve`, for its name. |
| `defattach` | None in the logic that proofs use. It changes which function ACL2 runs for a constrained function. | No statement. In program text, an `attach` line (section 4). |
| `deftheory`, `deflabel` | No. | `reserve`, for the name. |
| `verify-guards`, `set-body`, `in-theory`, `in-arithmetic-theory`, `theory-invariant`, `table`, `regenerate-tau-database`, `add-custom-keyword-hint`, `add-match-free-override`, `set-override-hints-macro`, `set-prover-step-limit`, `set-ruler-extenders`, `logic`, `program` | No. They guide ACL2's prover or say how later events are read. | No statement. |
| `add-include-book-dir`, `add-include-book-dir!`, `delete-include-book-dir`, `delete-include-book-dir!`, `comp`, `push-untouchable`, `remove-untouchable`, `reset-prehistory`, `value-triple` | No. They manage the session. | No statement. |

Around an event a book may write `local`, `skip-proofs`, `make-event`, and the forms `with-output`, `with-prover-step-limit`, `with-prover-time-limit`, `with-guard-checking-event`, `with-cbd` and `with-current-package`.

- **`local`.** A local event is absent from the book as other books see it. It has no logical content: it is something the author of the book gave ACL2's prover to work with. It becomes no statement. A proof may state its own lemmas and definitions (`formats.md`, section 6), and the local events of a book are suggestions for them.
- **`skip-proofs`.** The event inside becomes its statement, like any other. That ACL2 was told not to prove it changes nothing in ACL2 Core: a `theorem` statement needs a proof, or the verdict says that it was skipped.
- **`make-event`.** The event it expands to becomes the statement.
- **The others** change how ACL2 prints or how long it tries, and the event inside becomes its statement.

**Functions in program mode.** The world that ACL2 8.6 starts with holds 4,782 functions in program mode, and stores a body for none of them: what it keeps is the event that defined each, as its source wrote it. ACL2 lists 105 of them as functions with raw code: what such a function does is given by code in the Common Lisp under ACL2, which differs from its definition in ACL2's language, and ACL2's source says that they "should be executed only in raw Lisp". So program text cannot be had for every function in program mode, and a runner is not required to run every one. It runs the functions whose program text it is given, and refuses a call of any other. ACL2 runs a function in program mode as its Common Lisp code, where an `mbe` is its executable half, and the two halves need not agree; so the program text of a function in program mode is the body with each `mbe` replaced by its executable half (`EDGE-CASES.md`, entry 10.1). These counts are lines `count` of `checks/expected/facts.txt`.

**What a checker is told.** The statements of a book are written by ACL2 itself, which says what the book states once expanded. ACL2 has no part in finding or checking a proof. The step of `PLAN.md` that builds the exporter says how its output is compared with ACL2's world.
