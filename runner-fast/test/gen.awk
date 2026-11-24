# Writes the calls of one set of the fast runner's tests, one term a line,
# in the text of spec/formats.md.  From the root of the repository:
#
#     awk -v set=SET -f runner-fast/test/gen.awk > FILE
#
# SET names the set.  Each set has a number of calls and a seed of its
# own, given at the end of this file; -v n=N and -v seed=SEED put other
# whole numbers in their place.
#
# arith: calls of the arithmetic primitives binary-+, binary-*, <, unary--
# and unary-/ on integers and fractions near the edges of the fast
# runner's paths in machine words: 2^29, 10^9, 2^32, 10^18 and 2^63, with
# 2^64 and 10^27 beyond them.  A fraction is written in lowest terms.
#
# natives: calls of the functions that the fast runner computes natively:
# length, char, subseq, string-append, string< (alone, and through
# string>, string<= and string>=), nonnegative-integer-quotient (alone,
# and through floor, mod, truncate and rem), the four bitwise functions of
# two integers (alone, and through lognand, logorc1, logandc1 and lognor)
# and ash.  The arguments are strings of many lengths, pairs of strings
# that begin alike, integers whose quotient is at most 20,000 and shifts
# of at most 70 bits, on which the definitions finish quickly, and, in
# about a quarter of the calls, arguments on which the native forms must
# give way to the definitions: indices below zero, past the end, out of
# order or not integers, arguments that are not strings, divisors that are
# zero or negative, fractions, and shifts whose result is past 127 bits.
#
# large: calls of the quotient, of the bitwise functions and of ash on
# integers of up to 200 bits, positive and negative, drawn below 2^32,
# 2^59, 2^64, 2^127 and 2^200 or taken at 2^29, 10^18, 2^63, 2^64, 10^36,
# 2^126 and 2^127.  The definitions do not finish on them in any
# reasonable time or memory, or finish only because they divide by the
# native quotient.
#
# loop: calls of three functions of ACL2's library that call a native
# function again and again while they hold data of their own:
# explode-nonnegative-integer, which divides an integer of 4,000 digits by
# ten until nothing is left; logcount, which halves an integer of 4,000
# bits; and string-append-lst, which joins a thousand strings.  They make
# so many integers and strings that memory is collected many times inside
# the native functions.
#
# The values of the calls of large and loop are recorded
# (runner-fast/test/record.sh), so every awk must write the same file for
# the same set, count and seed.  To that end the numbers drawn come from a
# generator written here, not from rand; no number that awk computes
# passes 2^53, below which its arithmetic is exact; no number that awk
# writes as text passes 2^31; an integer beyond that is the text of its
# digits from start to finish, which the functions plus and times add and
# multiply; and no expression draws twice, so that the order in which an
# awk works out the parts of an expression does not matter.

# rnd(n): a whole number from 0 to n - 1, for n from 1 to 2147483646.
# The state X is a whole number from 1 to 2147483646, and X * 48271 is
# below 2^47.

function rnd(n) {
    X = (X * 48271) % 2147483647
    return X % n
}

function start(s,    i) {
    X = s % 2147483646 + 1
    for (i = 0; i < 16; i++) rnd(1)
}

# whole(s): the digits s without the zeros at their front.

function whole(s) {
    sub(/^0+/, "", s)
    return (s == "" ? "0" : s)
}

# digits(k): k digits, each drawn.

function digits(k,    s) {
    s = ""
    while (length(s) < k) s = s sprintf("%05d", rnd(100000))
    return substr(s, 1, k)
}

# times(s, m, c): s * m + c, for a whole number s in digits and whole
# numbers m and c below 10^9.

function times(s, m, c,    r, i, d) {
    r = ""
    for (i = length(s); i > 0; i -= 6) {
        d = (i > 6 ? substr(s, i - 5, 6) : substr(s, 1, i)) * m + c
        c = (d - d % 1000000) / 1000000
        r = sprintf("%06d", d % 1000000) r
    }
    return whole(c r)
}

# plus(s, t): s + t, for whole numbers s and t in digits.

function plus(s, t,    r, i, j, c, d) {
    r = ""
    c = 0
    i = length(s)
    j = length(t)
    while (i > 0 || j > 0) {
        d = c
        if (i > 0) d += (i > 6 ? substr(s, i - 5, 6) : substr(s, 1, i))
        if (j > 0) d += (j > 6 ? substr(t, j - 5, 6) : substr(t, 1, j))
        i -= 6
        j -= 6
        c = (d >= 1000000 ? 1 : 0)
        r = sprintf("%06d", d - c * 1000000) r
    }
    return whole(c r)
}

# big(top, bits): a whole number drawn from top * 2^bits to
# (top + 1) * 2^bits - 1, for a whole number top below 10^6.

function big(top, bits,    s, k, m, i) {
    s = top ""
    while (bits > 0) {
        k = (bits < 15 ? bits : 15)
        m = 1
        for (i = 0; i < k; i++) m *= 2
        s = times(s, m, rnd(m))
        bits -= k
    }
    return s
}

# two(k) is 2^k, and ones(k) is 2^k - 1.

function two(k,    s) {
    s = "1"
    while (k-- > 0) s = times(s, 2, 0)
    return s
}

function ones(k,    s) {
    s = "0"
    while (k-- > 0) s = times(s, 2, 1)
    return s
}

# low(s) and high(s): the last fifteen digits of s, and those before
# them, as numbers.

function low(s) {
    return (length(s) > 15 ? substr(s, length(s) - 14) : s) + 0
}

function high(s) {
    return (length(s) > 15 ? substr(s, 1, length(s) - 15) : 0) + 0
}

# coprime(s, t): whether the whole numbers s and t, above 0 and below
# 10^30, have no common factor.  Each is held as two numbers, a = ah *
# 10^15 + al.  While either passes 10^15 the larger gives way to half of
# the difference, halved until it is odd, which keeps the common factors
# of two odd numbers; then Euclid's algorithm finishes on al and bl.

function coprime(s, t,    ah, al, bh, bl, x) {
    ah = high(s)
    al = low(s)
    bh = high(t)
    bl = low(t)
    if (al % 2 == 0 && bl % 2 == 0) return 0
    while (al % 2 == 0) {
        al = al / 2 + (ah % 2) * 500000000000000
        ah = (ah - ah % 2) / 2
    }
    while (bl % 2 == 0) {
        bl = bl / 2 + (bh % 2) * 500000000000000
        bh = (bh - bh % 2) / 2
    }
    while (ah > 0 || bh > 0) {
        if (ah == bh && al == bl) return 0
        if (ah < bh || (ah == bh && al < bl)) {
            x = ah; ah = bh; bh = x
            x = al; al = bl; bl = x
        }
        ah -= bh
        al -= bl
        if (al < 0) {
            al += 1000000000000000
            ah--
        }
        while (al % 2 == 0) {
            al = al / 2 + (ah % 2) * 500000000000000
            ah = (ah - ah % 2) / 2
        }
    }
    while (bl > 0) {
        x = al % bl
        al = bl
        bl = x
    }
    return al == 1
}

function q(x) {
    return "(" Q " " x ")"
}

# The set arith.  natural(): a whole number near an edge, or of 1 to 20
# digits drawn.

function natural(    k) {
    if (rnd(2)) return whole(digits(1 + rnd(20)))
    k = 1 + rnd(8)
    if (k == 1) return rnd(7) ""
    return plus(EDGE[k], rnd(SPAN[k]) "")
}

# number(): an integer or, half the time, a fraction, of either sign.  A
# denominator that shares a factor with the numerator is drawn again.

function number(    m, d, sign) {
    m = natural()
    sign = (rnd(2) ? "-" : "")
    if (m == "0") return "0"
    if (rnd(2)) {
        d = natural()
        while (d == "0" || !coprime(m, d)) d = natural()
        if (d != "1") return sign m "/" d
    }
    return sign m
}

function arith(    a, b, f) {
    a = number()
    b = number()
    f = 1 + rnd(5)
    if (f > 3) print "(" ARITH[f] " " q(a) ")"
    else print "(" ARITH[f] " " q(a) " " q(b) ")"
}

# The set natives.  letters(k): k characters drawn.

function letters(k,    s) {
    s = ""
    while (k-- > 0) s = s substr(LETTERS, 1 + rnd(length(LETTERS)), 1)
    return s
}

# other(): a datum of any kind: a symbol, a number, a string, a character
# or a list.

function other() {
    return OTHER[1 + rnd(16)]
}

# place(size): an index into a string of size characters, at its ends or
# just past them, or, a quarter of the time, a datum of any kind.

function place(size,    k) {
    if (rnd(4) == 0) return other()
    k = rnd(5)
    if (k == 0) return 0
    if (k == 1) return size
    if (k == 2) return (size > 0 ? size - 1 : 0)
    if (k == 3) return size + 1
    return rnd(size + 3)
}

# part(s, i, j): the characters of s from the i-th to the j-th, which are
# none when j is below i.

function part(s, i, j) {
    return (i > j ? "" : substr(s, i, j - i + 1))
}

function natives(    kind, s, t, size, text, a, b, c, i, j, k, pair) {
    size = SIZE[1 + rnd(19)] + 0
    s = letters(size)
    text = 1
    a = "\"" s "\""
    if (rnd(10) == 0) {
        text = 0
        size = 3
        a = other()
    }
    kind = rnd(8)
    if (kind == 0) {
        print "(COMMON-LISP::LENGTH " q(a) ")"
    } else if (kind == 1) {
        print "(COMMON-LISP::CHAR " q(a) " " q(place(size)) ")"
    } else if (kind == 2) {
        i = place(size)
        j = place(size)
        if (rnd(10) < 6 && i ~ /^[0-9]+$/ && j ~ /^[0-9]+$/ && i + 0 > j + 0) {
            k = i; i = j; j = k
        }
        if (rnd(100) < 15) j = "COMMON-LISP::NIL"
        print "(COMMON-LISP::SUBSEQ " q(a) " " q(i) " " q(j) ")"
    } else if (kind == 3) {
        b = "\"" letters(SIZE[1 + rnd(19)] + 0) "\""
        if (rnd(10) == 0) b = other()
        print "(ACL2::STRING-APPEND " q(a) " " q(b) ")"
    } else if (kind == 4) {
        # A dividend and a divisor whose quotient is at most 20,000; a
        # fifth of the time a large divisor with a quotient of at most
        # 3,000; a quarter of the time a pair outside the native form.
        k = 1 + rnd(9)
        if (k > 8) j = 1 + rnd(100000)
        else j = SMALL[k] + 0
        i = rnd(20001) * j
        i += rnd(j)
        if (rnd(5) == 0) {
            j = LARGE[1 + rnd(6)]
            i = times(j, rnd(3001), 0)
            i = plus(i, whole(digits(length(j) - 1)))
        }
        if (rnd(4) == 0) {
            split(PAIR[1 + rnd(12)], pair, " ")
            i = pair[1]
            j = pair[2]
        }
        print "(" DIVIDE[1 + rnd(6)] " " q(i) " " q(j) ")"
    } else if (kind == 5) {
        i = small()
        j = small()
        if (rnd(100) < 15) i = NOINT[1 + rnd(5)]
        print "(" BITS[1 + rnd(8)] " " q(i) " " q(j) ")"
    } else if (kind == 6) {
        # A second string: drawn afresh, or one that begins as the first
        # does, or a datum of any kind.
        b = "\"" letters(SIZE[1 + rnd(19)] + 0) "\""
        k = rnd(10)
        if (k < 5 && text) {
            c = rnd(size + 1)
            k = rnd(4)
            if (k == 0) t = ""
            else if (k == 1) t = letters(1)
            else if (k == 2) t = part(s, c + 1, size)
            else t = part(s, c + 2, size) "z"
            b = "\"" part(s, 1, c) t "\""
        } else if (k == 5) {
            b = other()
        }
        print "(" ORDER[1 + rnd(5)] " " q(a) " " q(b) ")"
    } else {
        # A shift of at most 70 bits.  To the right, of an integer whose
        # quotient by the power of two is at most 20,000.
        k = rnd(13)
        if (k < 7) c = SHIFT[1 + k] + 0
        else if (k == 7) c = rnd(71)
        else if (k < 12) c = -SHIFT[k]
        else c = -1 - rnd(70)
        if (c < 0) {
            i = big(rnd(20001), -c)
        } else {
            k = rnd(5)
            if (k == 0) i = "0"
            else if (k == 1) i = "1"
            else if (k == 2) i = "255"
            else if (k == 3) i = rnd(16385) ""
            else i = big(0, 64)
        }
        if (rnd(10) < 3) i = "-" plus(i, "1")
        if (rnd(100) < 15) i = NOINT[1 + rnd(6)]
        if (rnd(10) == 0) c = NOINT[1 + rnd(4)]
        print "(COMMON-LISP::ASH " q(i) " " q(c) ")"
    }
}

# small(): an integer of at most 14 bits, of either sign.

function small(    k, v) {
    k = rnd(7)
    if (k == 0) v = 0
    else if (k == 1) v = 1
    else if (k == 2) v = 2
    else if (k == 3) v = 255
    else if (k == 4) v = rnd(257)
    else if (k == 5) v = rnd(4097)
    else v = rnd(16385)
    return (rnd(10) < 3 ? -v - 1 : v)
}

# The set large.  wide(): an integer of up to 200 bits, of either sign.

function wide(    k, s) {
    k = 1 + rnd(17)
    s = (k > 5 ? WIDE[k] : big(0, DRAWN[k] + 0))
    return (rnd(10) < 3 ? "-" plus(s, "1") : s)
}

function magnitude(s) {
    sub(/^-/, "", s)
    return s
}

function large(    i, j, k) {
    i = wide()
    j = wide()
    k = 1 + rnd(12)
    if (k > 10) {
        # A shift of up to 200 bits.
        k = 1 + rnd(21)
        if (k < 21) j = REACH[k]
        if (k == 12) j = rnd(131) ""
        if (k == 21) j = "-" (1 + rnd(200))
        print "(COMMON-LISP::ASH " q(i) " " q(j) ")"
    } else if (k > 4 && k < 7) {
        print "(ACL2::NONNEGATIVE-INTEGER-QUOTIENT " q(magnitude(i)) " " q(plus(magnitude(j), "1")) ")"
    } else {
        if (k > 6 && j == "0") j = "1"
        print "(" WHOLE[k] " " q(i) " " q(j) ")"
    }
}

# The set loop.

function loop(k,    i, s) {
    if (k % 3 == 0) {
        s = 1 + rnd(9)
        s = s digits(3999)
        print "(COMMON-LISP::COERCE (ACL2::EXPLODE-NONNEGATIVE-INTEGER " q(s) " " q(10) " " \
              q("COMMON-LISP::NIL") ") " q("COMMON-LISP::STRING") ")"
    } else if (k % 3 == 1) {
        print "(COMMON-LISP::LOGCOUNT " q(big(1, 3999)) ")"
    } else {
        s = ""
        for (i = 0; i < 1000; i++) s = s (i > 0 ? " " : "") "\"" letters(rnd(61)) "\""
        print "(ACL2::STRING-APPEND-LST " q("(" s ")") ")"
    }
}

BEGIN {
    Q = "COMMON-LISP::QUOTE"
    LETTERS = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789 -_.:;,()[]{}<>!?#$%&*+=/'^~|@`"

    # arith.  Each edge is the least of a run of whole numbers and the
    # length of the run: 2^29 - 4 to 2^29 + 4, 10^9 - 4 to 10^9 + 4,
    # 2^32 - 4 to 2^32 + 3, 10^18 - 4 to 10^18 + 4, 2^63 - 4 to 2^63 + 3,
    # 2^64 + 4 to 2^64 + 10, and 10^27 to 10^27 + 6.  The first run, 0 to
    # 6, is drawn in natural().
    split("0 536870908 999999996 4294967292 999999999999999996 9223372036854775804" \
          " 18446744073709551620 1000000000000000000000000000", EDGE, " ")
    split("7 9 9 8 9 8 7 7", SPAN, " ")
    split("ACL2::BINARY-+ ACL2::BINARY-* COMMON-LISP::< ACL2::UNARY-- ACL2::UNARY-/", ARITH, " ")

    # natives.
    split("0 0 1 2 3 4 5 7 8 9 15 16 17 31 33 64 100 257 1000", SIZE, " ")
    split("COMMON-LISP::NIL,COMMON-LISP::T,-1,-7,1/2,-3/4,\"x\",ACL2::A,(1 2 3),(#\\61 #\\62),3000,#\\61," \
          "(ACL2::A . 5),0,1,5", OTHER, ",")
    split("1/2,ACL2::A,COMMON-LISP::NIL,\"x\",(1 2),-7/3", NOINT, ",")
    split("1 2 3 7 10 16 255 1000", SMALL, " ")
    split("1000000000 1000000000000000000 18446744073709551616 1000000000000000000000000000007 536870912" \
          " 300000000000000000", LARGE, " ")
    split("0 0,5 0,-17 5,17 -5,-17 -5,7/2 2,7 1/3,ACL2::A 3,9 \"x\",0 7,6 6,5 6", PAIR, ",")
    split("ACL2::NONNEGATIVE-INTEGER-QUOTIENT ACL2::NONNEGATIVE-INTEGER-QUOTIENT COMMON-LISP::FLOOR" \
          " COMMON-LISP::MOD COMMON-LISP::TRUNCATE COMMON-LISP::REM", DIVIDE, " ")
    split("ACL2::BINARY-LOGAND ACL2::BINARY-LOGIOR ACL2::BINARY-LOGXOR ACL2::BINARY-LOGEQV" \
          " COMMON-LISP::LOGNAND COMMON-LISP::LOGORC1 COMMON-LISP::LOGANDC1 COMMON-LISP::LOGNOR", BITS, " ")
    split("COMMON-LISP::STRING< COMMON-LISP::STRING< COMMON-LISP::STRING> COMMON-LISP::STRING<=" \
          " COMMON-LISP::STRING>=", ORDER, " ")
    split("0 1 2 8 13 32 56 1 2 5 8", SHIFT, " ")

    # large.  The first five integers of wide() are drawn below 2 to
    # these powers; the others are these.
    split("32 59 64 127 200", DRAWN, " ")
    WIDE[6] = "1000000000000000000"
    WIDE[7] = "999999999999999999"
    WIDE[8] = two(63)
    WIDE[9] = ones(64)
    WIDE[10] = "536870911"
    WIDE[11] = "536870912"
    WIDE[12] = "999999999999999999999999999999999999"
    WIDE[13] = "1000000000000000000000000000000000000"
    WIDE[14] = two(126)
    WIDE[15] = times(ones(126), 2, 0)
    WIDE[16] = ones(127)
    WIDE[17] = two(127)
    split("ACL2::BINARY-LOGAND ACL2::BINARY-LOGIOR ACL2::BINARY-LOGXOR ACL2::BINARY-LOGEQV - -" \
          " COMMON-LISP::FLOOR COMMON-LISP::MOD COMMON-LISP::TRUNCATE COMMON-LISP::REM", WHOLE, " ")
    split("0 1 7 13 32 63 64 100 126 127 128 - -1 -13 -32 -63 -64 -126 -127 -128", REACH, " ")

    # The sets: the number of calls and the seed of each.
    if (set == "arith") { count = 20000; first = 20261122 }
    else if (set == "natives") { count = 10000; first = 11 }
    else if (set == "large") { count = 4000; first = 5 }
    else if (set == "loop") { count = 12; first = 3 }
    else {
        print "gen.awk: set must be arith, natives, large or loop" | "cat 1>&2"
        exit 2
    }
    if (n != "") count = n + 0
    if (seed != "") first = seed + 0
    start(first)
    for (call = 0; call < count; call++) {
        if (set == "arith") arith()
        else if (set == "natives") natives()
        else if (set == "large") large()
        else loop(call)
    }
}
