# The printer and reader

Run `sh export/proofs/round-trip.sh` from the repository root with ACL2 8.7. It certifies the round-trip books beside the printer and the exporter core, with copies of the checker's `base` and `read` books. It checks the certificate annotations, the printer's guards, and the theorem hypotheses on actual ACL2 package declarations.

## The round trip

- **`rt-parse-printed-line`** proves that `boymoo::parse-line` applied to the characters of `(bm-line word args)` and one line feed returns the word's tag followed by the reader's form of `args`. The word must be admitted and the arguments must be a proper list of format data. Each written symbol must have a package declaration that imports no symbol of that name, with the corresponding import index. [Statement](round-trip-packages.lisp)
- **`rt-parse-printed-line-with-package-index`** gives the same result under the weaker package condition that each written symbol's package lookup finds a record and its import lookup finds no entry. [Statement](round-trip.lisp)
- **`rt-package-index-agrees-with-declarations`** proves that, for a record with the index built from its declarations, the reader's package check is equivalent to the declaration rule of [language section 2](../../spec/language.md). Each index entry is the singleton list of the imported symbol. The `acl2-package-imports` test checks the startup record for `ACL2` and confirms that the reader refuses `ACL2::CAR` and `ACL2::NIL`. [Statement](round-trip-packages.lisp)
- **`rt-datum-form-injective`** proves that two format data have equal reader forms exactly when they are equal ACL2 objects. It requires no word or package table. [Statement](round-trip-symbols.lisp)

The datum map `rt-datum-form` leaves numbers, characters, and strings as themselves and maps both sides of a cons. For each symbol it constructs the qualified spelling from [format section 2](../../spec/formats.md). The spellings `COMMON-LISP::NIL` and `COMMON-LISP::T` map to ACL2's `NIL` and `T`. Every other qualified spelling is interned as a symbol name using the `BOYMOO` package. The definition calls neither program. The injectivity proof recovers the two parts of each spelling and uses ACL2's interning axiom to identify native symbols with the same names.

## Accepted lines

- **`rt-accepted-line-has-reader-text`** proves that every line accepted by `parse-line` is recovered character for character from the consumed word spelling and the returned reader data. **`rt-accepted-arguments-are-in-table`** proves that the arguments form a proper list of format data in the reader's representation and that every written symbol passed the package lookup. **`rt-accepted-line-has-format-word`** proves that the spelling is a format word if the word table has no empty key. [Statements](round-trip-converse.lisp)
- **`rt-accepted-line-with-native-names-is-printer-text`** proves that an accepted line with a format word is the text of `bm-line` and one line feed when each read symbol's name is available in its native ACL2 package. The theorem constructs the proper list of native arguments with `rt-native-datum` and proves that their reader form is exactly the returned arguments. [Statement](round-trip-native.lisp)
- **`rt-accepted-line-with-compatible-packages-is-printer-text`** proves the native converse for every accepted line if the word table has no empty key and the package table is compatible with ACL2. It also proves that the reconstructed native data satisfy the forward theorem's declaration condition. [Statement](round-trip-native.lisp)
- **`rt-accepted-line-is-printer-text`** gives the same text equality if a proper native list of format data is supplied whose reader form matches the returned arguments and the consumed spelling is a format word. [Statement](round-trip-converse.lisp)

For an ordinary represented symbol, `rt-native-datum` decodes the package name and symbol name and interns the name using ACL2's `pkg-witness`. The condition `rt-native-names-p` requires a nonempty package name and checks that this interning gives a symbol of that home package. The special symbols `NIL` and `T` are already native. **`rt-native-datum-inverts-datum-form`** proves that any native datum in the format has available names in its reader form and that recovering them gives the original datum. Thus the name condition is necessary for a native preimage as well as sufficient on the arguments of an accepted line. [Statement](round-trip-native.lisp)

A compatible table, as defined by `rt-compatible-package-table-p`, has nonempty package keys and import indexes built from each record's declarations. For each of its packages, the declarations include every name that ACL2 imports into the package of that name. Reader declarations may also exclude additional names. Each accepted owned name is therefore available to the native constructor. [Definition](round-trip-native.lisp)

### An import conflict

An index can agree with its declaration while that declaration permits a name which ACL2 imports from another package. Declare `BOYMOO` with no imports in the reader's table. The reader accepts `(reserve BOYMOO::CAR)` with a line feed. In the ACL2 session running the checker, `BOYMOO` imports `COMMON-LISP::CAR`, so there is no native `BOYMOO::CAR`. **`rt-conflicting-native-import-is-read`** certifies acceptance with the declared index, and **`rt-conflicting-native-import-has-no-preimage`** proves that no native format datum has the returned argument list as its reader form. The `native-import-conflict` test exercises the same conditions. [Counterexample](round-trip-native.lisp)

```lisp
(let* ((pkgs (boymoo::trie-put (coerce "BOYMOO" 'list)
                               (list nil nil nil nil) nil))
       (words (list (cons (coerce "reserve" 'list) :reserve)))
       (line (append (coerce "(reserve BOYMOO::CAR)" 'list) '(#\Newline)))
       (read (boymoo::parse-line line words pkgs)))
  (list (rt-package-index-of-its-imports-p "BOYMOO" pkgs)
        read (rt-native-names-p (cdr read))))
```

This form gives `(T (:RESERVE BOYMOO::|BOYMOO::CAR|) NIL)` in ACL2 8.7. To evaluate it, run `sh export/proofs/round-trip.sh`, then load `checker/package.lsp` and include `build/export/acl2/round-trip-native` from the repository root.

## Domain and tests

| Hypothesis | Meaning and test |
|---|---|
| Format word and admission | `rt-word-p` requires a nonempty string of lowercase ASCII letters and hyphens. `rt-word-admitted-p` requires an entry for the spelling, with the tag in the cdr. `startup-world` and `world-with-books` check these conditions and compare the parsed tag and recovered spelling. |
| Format data and proper argument list | `true-listp` and `rt-format-datum-p` require a proper list of integers, fractions, complex rationals, characters, strings, ACL2 symbols with nonempty home-package names, and conses of those data. The world tests cover all the kinds, including nested proper and dotted conses, empty and escaped symbol names, and character codes 128 and 255. They also compare the reader forms of equal and unequal pairs of data. |
| Reader package lookup and declaration coverage | The world tests make package records from ACL2's `known-package-alist`, index the native import names as singletons, and check both `rt-written-symbols-pass-index-p` and `rt-declarations-cover-written-symbols-p`. Hidden reader records are included. `hidden-reader-package` tests an owned name, a missing declaration, and an imported name. |
| A word table with no empty key and a compatible package table | `startup-world` checks the word table's empty lookup. Both world tests check every record of the tables they construct for package compatibility. |
| Availability of native names and reconstruction | The world tests check availability on the returned arguments and compare `rt-native-datum` of those arguments with the native input list. They reconstruct its text using the reader-form renderer. `noncanonical-text` checks rejection of cases including a leading zero, an unreduced fraction, an unnecessary escape, and a dotted `NIL`. |

The `startup-world` test uses the package declarations ACL2 starts with. `world-with-books` checks the world after including `arithmetic/rationals`, `std/osets/top`, and `std/strings/pretty` from `export/books.txt`. It exercises symbols from `SET` and `STR`. The theorems take package and word tables and require no predicate on the shape of ACL2's world.

ACL2's bad atoms and Lisp objects outside ACL2's logical data are outside the datum domain. Every character code from 0 through 255 is included in the proofs, including within strings and symbol names. The printer uses ASCII escapes for codes outside the literal range. An implicit `NIL` ending a proper list needs no declaration. An explicit `NIL` datum needs one. The `empty-table-keys` test supplies artificial empty keys and shows acceptance of `()` and `(theorem ||::X)` with line feeds. The format word and native package conditions exclude those cases.

The `line-feed` test checks that `(bm-line "theorem" nil)` gives `"(theorem)"` and that only appending the file writer's line feed makes this input a complete line. The hypotheses and conclusions concern ACL2 characters. Disk I/O and admission of the statements or proof steps described by a line are outside their scope.

The proofs use the logical ACL2 functions `symbol-package-name`, `pkg-witness`, and `pkg-imports`. Executing the latter two depends on package visibility in the ACL2 session. The top-level evaluator can also refuse the home-package lookup of a hidden symbol with guard checking completely off. After `sh export/proofs/round-trip.sh` and `sh checks/run.sh`, these ACL2 forms exercise the two guard settings from the repository root.

```lisp
(include-book "build/edge-hidden")
(include-book "build/export/acl2/canon")
(set-guard-checking t)
(assert-event (equal (bm-line "theorem" (list (bm-hidden-symbol)))
                     "(theorem BM-HIDDEN::FOO)"))
(set-guard-checking :none)
(bm-line "theorem" (list (bm-hidden-symbol)))
```

The assertion passes and the final call signals ACL2's unknown-package error. This was checked on 2026-11-20.

## Printer guards and checksums

ACL2 verifies all twelve guards in [canon.lisp](../../checks/canon.lisp). The guard proof checks the bounds of the hexadecimal indices and shows that each printing step preserves an accumulator of characters. The logical arm of the bad-atom branch calls `illegal`, and `bm-bad-datum-error-equals-illegal` proves equality with the executable hard error for every argument. The `printer-guards` test checks all twelve functions' guard status in the certified book.

On 2026-11-20, `sh export/proofs/round-trip.sh` reported `all round-trip checks passed`. The certificate checks found zero skipped proofs, added axioms, or trust tags. The nine proof books have 2,710 lines and 116,876 bytes by `wc -l -c export/proofs/round-trip*.lisp`. The script reported 3.96 seconds of ACL2 certification time across those books.

On the same date, `sh checks/run.sh` reported `all checks passed`, and `sh checker/test.sh` reported `all checker tests passed` with the expected verdict for each of its 319 cases. The library statements, program text, and notes matched their manifest entries using the following commands.

```sh
mkdir -p build/export
names=$(sed -n 's/^(define [^ (][^ ]* (\([^ ]*\) .*/\1/p; s/^(define ([^()]*) (\([^ ]*\) .*/\1/p' \
    spec/ground.txt | tr '\n' ' ')
printf "(assign bx-ground-fns '(%s))\n" "$names" > build/export/ground-fns.lsp
sh export/book.sh :library
python3 - <<'PY'
import hashlib
from pathlib import Path

files = {"build/export/library." + kind for kind in ("notes", "program", "statements")}
checked = set()
for entry in Path("build/4b-baseline.sha256").read_text().splitlines():
    digest, name = entry.split()
    if name in files:
        if hashlib.sha256(Path(name).read_bytes()).hexdigest() != digest:
            raise SystemExit(name + ": checksum mismatch")
        print(name + ": OK")
        checked.add(name)
if checked != files:
    raise SystemExit("The manifest is missing library checksums")
PY
```
