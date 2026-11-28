set -eu
export LC_ALL=C

dir=build/compiler/numbers-test
mkdir -p "$dir"
runner=build/runner/boymoo-run
compiler=build/compiler
export TMPDIR="$PWD/$dir"

# The printer uses signed binary for integers, including character codes.
# It uses delimiters for the parts of fractions, complex rationals and conses.
# Strings are lists of printed characters enclosed in brackets.
cat > "$dir/program" <<'PROGRAM'
(define COMMON-LISP::NIL (BOYMOO-COMPILER::BITS (ACL2::N ACL2::OUT) (COMMON-LISP::IF (COMMON-LISP::EQUAL ACL2::N (COMMON-LISP::QUOTE 0)) ACL2::OUT (BOYMOO-COMPILER::BITS (COMMON-LISP::ASH ACL2::N (COMMON-LISP::QUOTE -1)) (COMMON-LISP::CONS (COMMON-LISP::CODE-CHAR (ACL2::BINARY-+ (COMMON-LISP::QUOTE 48) (ACL2::BINARY-LOGXOR ACL2::N (COMMON-LISP::ASH (COMMON-LISP::ASH ACL2::N (COMMON-LISP::QUOTE -1)) (COMMON-LISP::QUOTE 1))))) ACL2::OUT)))))
(define COMMON-LISP::NIL (BOYMOO-COMPILER::PRINT-INTEGER (ACL2::N ACL2::OUT) (COMMON-LISP::IF (COMMON-LISP::< ACL2::N (COMMON-LISP::QUOTE 0)) (COMMON-LISP::CONS (COMMON-LISP::QUOTE #\2D) (BOYMOO-COMPILER::BITS (ACL2::UNARY-- ACL2::N) ACL2::OUT)) (COMMON-LISP::IF (COMMON-LISP::EQUAL ACL2::N (COMMON-LISP::QUOTE 0)) (COMMON-LISP::CONS (COMMON-LISP::QUOTE #\30) ACL2::OUT) (BOYMOO-COMPILER::BITS ACL2::N ACL2::OUT)))))
(define COMMON-LISP::NIL (BOYMOO-COMPILER::PRINT-RATIONAL (ACL2::X ACL2::OUT) (COMMON-LISP::IF (COMMON-LISP::INTEGERP ACL2::X) (BOYMOO-COMPILER::PRINT-INTEGER ACL2::X ACL2::OUT) (BOYMOO-COMPILER::PRINT-INTEGER (COMMON-LISP::NUMERATOR ACL2::X) (COMMON-LISP::CONS (COMMON-LISP::QUOTE #\2F) (BOYMOO-COMPILER::PRINT-INTEGER (COMMON-LISP::DENOMINATOR ACL2::X) ACL2::OUT))))))
(define COMMON-LISP::NIL (BOYMOO-COMPILER::PRINT-CHARACTER (ACL2::X ACL2::OUT) (COMMON-LISP::CONS (COMMON-LISP::QUOTE #\40) (BOYMOO-COMPILER::PRINT-INTEGER (COMMON-LISP::CHAR-CODE ACL2::X) ACL2::OUT))))
(define COMMON-LISP::NIL (BOYMOO-COMPILER::PRINT-STRING (ACL2::X ACL2::OUT) (COMMON-LISP::IF (COMMON-LISP::CONSP ACL2::X) (BOYMOO-COMPILER::PRINT-CHARACTER (COMMON-LISP::CAR ACL2::X) (BOYMOO-COMPILER::PRINT-STRING (COMMON-LISP::CDR ACL2::X) ACL2::OUT)) ACL2::OUT)))
(define COMMON-LISP::NIL (BOYMOO-COMPILER::PRINT-NUMBER-TEST (ACL2::X ACL2::OUT) (COMMON-LISP::IF (COMMON-LISP::RATIONALP ACL2::X) (BOYMOO-COMPILER::PRINT-RATIONAL ACL2::X ACL2::OUT) (COMMON-LISP::IF (ACL2::COMPLEX-RATIONALP ACL2::X) (COMMON-LISP::CONS (COMMON-LISP::QUOTE #\7B) (BOYMOO-COMPILER::PRINT-RATIONAL (COMMON-LISP::REALPART ACL2::X) (COMMON-LISP::CONS (COMMON-LISP::QUOTE #\2C) (BOYMOO-COMPILER::PRINT-RATIONAL (COMMON-LISP::IMAGPART ACL2::X) (COMMON-LISP::CONS (COMMON-LISP::QUOTE #\7D) ACL2::OUT))))) (COMMON-LISP::IF (COMMON-LISP::CONSP ACL2::X) (COMMON-LISP::CONS (COMMON-LISP::QUOTE #\28) (BOYMOO-COMPILER::PRINT-NUMBER-TEST (COMMON-LISP::CAR ACL2::X) (COMMON-LISP::CONS (COMMON-LISP::QUOTE #\20) (BOYMOO-COMPILER::PRINT-NUMBER-TEST (COMMON-LISP::CDR ACL2::X) (COMMON-LISP::CONS (COMMON-LISP::QUOTE #\29) ACL2::OUT))))) (COMMON-LISP::IF (COMMON-LISP::STRINGP ACL2::X) (COMMON-LISP::CONS (COMMON-LISP::QUOTE #\5B) (BOYMOO-COMPILER::PRINT-STRING (COMMON-LISP::COERCE ACL2::X (COMMON-LISP::QUOTE COMMON-LISP::LIST)) (COMMON-LISP::CONS (COMMON-LISP::QUOTE #\5D) ACL2::OUT))) (COMMON-LISP::IF (COMMON-LISP::CHARACTERP ACL2::X) (BOYMOO-COMPILER::PRINT-CHARACTER ACL2::X ACL2::OUT) (COMMON-LISP::CONS (COMMON-LISP::IF ACL2::X (COMMON-LISP::QUOTE #\54) (COMMON-LISP::QUOTE #\4E)) ACL2::OUT))))))))
(define COMMON-LISP::NIL (BOYMOO-COMPILER::NUMBER-COLLECTION-CASE (ACL2::N ACL2::X) (COMMON-LISP::IF (COMMON-LISP::EQUAL ACL2::N (COMMON-LISP::QUOTE 0)) ACL2::X (BOYMOO-COMPILER::NUMBER-COLLECTION-CASE (ACL2::BINARY-+ ACL2::N (COMMON-LISP::QUOTE -1)) (ACL2::BINARY-+ ACL2::X (COMMON-LISP::QUOTE #C(18446744073709551616/3 1/2)))))))
PROGRAM

# Each operand is exercised by every numeric primitive and jet. Pairs
# also test equality across immediate, boxed, rational and complex results.
awk '
    function call(f, a, b, c) {
        return "(" f " " a (b == "" ? "" : " " b) (c == "" ? "" : " " c) ")"
    }
    function quote(s) { return call("COMMON-LISP::QUOTE", s) }
    function cons(a, b) { return call("COMMON-LISP::CONS", a, b) }
    function result(v) { results[++count] = v }
    BEGIN {
        x = "ACL2::X"
        y = "ACL2::Y"
        nil = quote("COMMON-LISP::NIL")
        unary_count = split("ACL2::ACL2-NUMBERP ACL2::COMPLEX-RATIONALP ACL2::UNARY-- ACL2::UNARY-/ COMMON-LISP::INTEGERP COMMON-LISP::RATIONALP COMMON-LISP::NUMERATOR COMMON-LISP::DENOMINATOR COMMON-LISP::REALPART COMMON-LISP::IMAGPART COMMON-LISP::CODE-CHAR COMMON-LISP::CHAR-CODE COMMON-LISP::LENGTH COMMON-LISP::CAR COMMON-LISP::CDR COMMON-LISP::CONSP COMMON-LISP::SYMBOLP COMMON-LISP::STRINGP COMMON-LISP::CHARACTERP", unary, " ")
        for (i = 1; i <= unary_count; i++) result(call(unary[i], x))
        binary_count = split("ACL2::BINARY-+ ACL2::BINARY-* COMMON-LISP::< COMMON-LISP::COMPLEX COMMON-LISP::EQUAL ACL2::BINARY-LOGXOR", binary, " ")
        for (i = 1; i <= binary_count; i++) result(call(binary[i], x, y))
        result(call("COMMON-LISP::ASH", x, quote("-67")))
        result(call("COMMON-LISP::ASH", x, quote("37")))
        result(call("COMMON-LISP::CHAR", quote("\"X\""), x))
        result(call("COMMON-LISP::COERCE", x, quote("COMMON-LISP::STRING")))
        body = nil
        for (i = count; i > 0; i--) body = cons(results[i], body)
        printf "(define COMMON-LISP::NIL (BOYMOO-COMPILER::NUMBER-PAIR (%s %s) %s))\n", x, y, body
    }
    {
        split($0, pair, "|")
        entries[++rows] = call("BOYMOO-COMPILER::NUMBER-PAIR", quote(pair[1]), quote(pair[2]))
    }
    END {
        string = quote("\"AB\"")
        entries[++rows] = call("COMMON-LISP::SUBSEQ", string, quote("1/2"), quote("3/2"))
        entries[++rows] = call("COMMON-LISP::SUBSEQ", string, quote("18446744073709551616"), nil)
        entries[++rows] = call("COMMON-LISP::SUBSEQ", string, quote("18446744073709551616"), quote("18446744073709551617"))
        entries[++rows] = call("COMMON-LISP::SUBSEQ", string, quote("#C(1 1)"), quote("#C(2 1)"))
        entries[++rows] = call("COMMON-LISP::SUBSEQ", quote("(4 5 . 6)"), quote("COMMON-LISP::T"), quote("3"))
        entries[++rows] = call("COMMON-LISP::SUBSEQ", quote("1/2"), quote("-1"), nil)
        entries[++rows] = call("COMMON-LISP::ASH", quote("1"), quote("-4611686018427387905"))
        entries[++rows] = call("COMMON-LISP::ASH", quote("-1"), quote("-100000000000000000000"))
        entries[++rows] = call("COMMON-LISP::ASH", quote("0"), quote("100000000000000000000"))
        entries[++rows] = call("COMMON-LISP::ASH", quote("4611686018427387904"), quote("3/4"))
        entries[++rows] = call("COMMON-LISP::ASH", quote("4611686018427387904"), quote("#C(0 1)"))
        entries[++rows] = call("COMMON-LISP::ASH", quote("-18446744073709551615"), quote("-32"))
        entries[++rows] = call("ACL2::BINARY-LOGXOR", quote("18446744073709551615"), quote("-1"))
        entries[++rows] = call("COMMON-LISP::FLOOR", quote("7"), quote("2"))
        number = quote("18446744073709551616")
        entries[++rows] = call("ACL2::BAD-ATOM<=", number, number)
        entries[++rows] = call("ACL2::INTERN-IN-PACKAGE-OF-SYMBOL", string, number)
        entries[++rows] = call("ACL2::PKG-IMPORTS", number)
        entries[++rows] = call("COMMON-LISP::SYMBOLP", call("ACL2::PKG-WITNESS", number))
        entries[++rows] = call("COMMON-LISP::SYMBOL-NAME", number)
        entries[++rows] = call("ACL2::SYMBOL-PACKAGE-NAME", number)
        entries[++rows] = call("COMMON-LISP::EQUAL", call("ACL2::BINARY-+", quote("4611686018427387903"), quote("1")), quote("4611686018427387904"))
        entries[++rows] = call("COMMON-LISP::EQUAL", call("ACL2::BINARY-*", quote("3/2"), quote("1/2")), quote("3/4"))
        entries[++rows] = call("COMMON-LISP::EQUAL", call("COMMON-LISP::COMPLEX", quote("0"), quote("1")), quote("#C(0 1)"))
        entries[++rows] = call("BOYMOO-COMPILER::NUMBER-COLLECTION-CASE", quote("800"), quote("#C(0 1)"))
        body = nil
        for (i = rows; i > 0; i--) body = cons(entries[i], body)
        body = call("BOYMOO-COMPILER::PRINT-NUMBER-TEST", body, nil)
        printf "(define COMMON-LISP::NIL (BOYMOO-COMPILER::NUMBER-TEST (ACL2::INPUT) %s))\n", call("COMMON-LISP::COERCE", body, quote("COMMON-LISP::STRING"))
    }
' <<'CASES' >> "$dir/program"
0|1
1|-1
-1|-1
4611686018427387903|1
4611686018427387904|0
4611686018427387905|-4611686018427387904
-4611686018427387903|-1
-4611686018427387904|-1
-4611686018427387905|4611686018427387905
9223372036854775808|-9223372036854775808
-9223372036854775808|2
18446744073709551616|-18446744073709551616
-18446744073709551616|18446744073709551616
340282366920938463463374607431768211456|100000000000000000000
-340282366920938463463374607431768211456|-340282366920938463463374607431768211456
100000000000000000000|-100000000000000000000
-100000000000000000000|1
3/4|-5/6
-5/6|5/6
18446744073709551617/18446744073709551616|18446744073709551616/18446744073709551617
#C(0 1)|#C(0 -1)
#C(3/4 -5/6)|#C(3/4 5/6)
#C(18446744073709551617 1/2)|-3/4
COMMON-LISP::NIL|1/2
"AB"|#\58
#\FF|COMMON-LISP::T
(1 3/4 . 2)|1
CASES

awk '/^\((package|hidden-package) /' spec/ground.txt "$compiler/compiler.statements" > "$dir/input"
cat "$compiler/ground.program" "$compiler/library.statements" "$dir/program" >> "$dir/input"
printf '(entry BOYMOO-COMPILER::NUMBER-TEST)\n' >> "$dir/input"
printf '(BOYMOO-COMPILER::NUMBER-TEST (COMMON-LISP::QUOTE ""))\n' > "$dir/term"
"$runner" -j -p spec/ground.txt -p "$compiler/compiler.statements" \
    "$compiler/ground.program" "$compiler/library.statements" "$dir/program" \
    < "$dir/term" > "$dir/reference.string"
# The printer emits printable characters without quotes or escapes.
awk 'NR != 1 || $0 !~ /^"[^"\\]*"$/ { exit 1 }
     { printf "%s", substr($0, 2, length($0) - 2) }
     END { if (NR != 1) exit 1 }' "$dir/reference.string" > "$dir/reference"

sh compiler/compile.sh "$dir/input" > "$dir/executable"
chmod +x "$dir/executable"
: > "$dir/empty"
"$dir/executable" < "$dir/empty" > "$dir/compiled"
cmp "$dir/reference" "$dir/compiled"
printf 'Numeric primitives and jets agree on %d bytes of results.\n' \
    "$(wc -c < "$dir/compiled")"
