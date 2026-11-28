#!/bin/sh
set -eu
export LC_ALL=C

sh compiler/build.sh -d build/compiler/a64 -x a64
dir=build/compiler/a64
export TMPDIR="$PWD/$dir"

cat > "$dir/examples" <<'EXAMPLES'
Lstart:|(KEYWORD::LABEL "start")
movz x12, #0xabcd|(KEYWORD::MOVZ 12 43981 0)
movk x12, #0xfedc, lsl #48|(KEYWORD::MOVK 12 65244 48)
movn x5, #0x5678, lsl #32|(KEYWORD::MOVN 5 22136 32)
mov x2, x5|(KEYWORD::MOV 2 5)
mov x9, sp|(KEYWORD::MOV-SP 9 31)
add x2, x20, #0xafe|(KEYWORD::ADD 2 20 2814)
sub sp, sp, #0xe20|(KEYWORD::SUB 31 31 3616)
adds x3, x9, #1|(KEYWORD::ADDS 3 9 1)
subs xzr, x9, #2|(KEYWORD::SUBS 31 9 2)
cmp x19, #4095|(KEYWORD::CMP 19 4095)
cmn x20, #1|(KEYWORD::CMN 20 1)
tst xzr, xzr; ccmp xzr, xzr, #8, ne|(KEYWORD::CMP 31 5)
movz x9, #7; subs x9, xzr, x9|(KEYWORD::SUBS 9 31 7)
add x10, x10, x20, lsl #2|(KEYWORD::ADD-REG 10 10 20 2)
sub x10, x10, x20, lsl #63|(KEYWORD::SUB-REG 10 10 20 63)
adds x10, x10, x20, lsl #5|(KEYWORD::ADDS-REG 10 10 20 5)
subs x10, x10, x20, lsl #6|(KEYWORD::SUBS-REG 10 10 20 6)
cmp x10, x9|(KEYWORD::CMP-REG 10 9)
neg x10, x9|(KEYWORD::NEG 10 9)
and x10, x9, x20|(KEYWORD::AND-REG 10 9 20)
orr x10, x9, x20|(KEYWORD::ORR-REG 10 9 20)
eor x10, x9, x20|(KEYWORD::EOR-REG 10 9 20)
ands x10, x9, x20|(KEYWORD::ANDS-REG 10 9 20)
tst x9, x20|(KEYWORD::TST-REG 9 20)
mvn x10, x9|(KEYWORD::MVN 10 9)
and x10, x9, #0x7fffffffffffffff|(KEYWORD::AND-MASK 10 9 63)
tst x9, #7|(KEYWORD::TST-MASK 9 3)
and xzr, x9, xzr|(KEYWORD::AND-MASK 31 9 8)
lsl x10, x9, #43|(KEYWORD::LSL 10 9 43)
lsr x10, x9, #58|(KEYWORD::LSR 10 9 58)
asr x10, x9, #63|(KEYWORD::ASR 10 9 63)
lslv x10, x9, x20|(KEYWORD::LSLV 10 9 20)
lsrv x10, x9, x20|(KEYWORD::LSRV 10 9 20)
asrv x10, x9, x20|(KEYWORD::ASRV 10 9 20)
clz x10, x9|(KEYWORD::CLZ 10 9)
mul x10, x9, x20|(KEYWORD::MUL 10 9 20)
smulh x10, x9, x20|(KEYWORD::SMULH 10 9 20)
sdiv x10, x9, x20|(KEYWORD::SDIV 10 9 20)
udiv x10, x9, x20|(KEYWORD::UDIV 10 9 20)
msub x10, x9, x20, x5|(KEYWORD::MSUB 10 9 20 5)
csel x10, x9, x20, hs|(KEYWORD::CSEL 10 9 20 KEYWORD::HS)
cset x10, gt|(KEYWORD::CSET 10 KEYWORD::GT)
ldr x9, [x19, #32760]|(KEYWORD::LDR 9 19 32760)
str x2, [x9, #520]|(KEYWORD::STR 2 9 520)
ldr x9, [sp, x20]|(KEYWORD::LDR-REG 9 31 20)
str x9, [x2, x20]|(KEYWORD::STR-REG 9 2 20)
ldrb w0, [sp, #4095]|(KEYWORD::LDRB 0 31 4095)
strb w0, [x11, #260]|(KEYWORD::STRB 0 11 260)
ldrb w0, [x2, x20]|(KEYWORD::LDRB-REG 0 2 20)
strb w0, [x2, x20]|(KEYWORD::STRB-REG 0 2 20)
ldur x9, [x19, #-256]|(KEYWORD::LDUR 9 19 -256)
stur x2, [sp, #255]|(KEYWORD::STUR 2 31 255)
ldurb w0, [x11, #-1]|(KEYWORD::LDURB 0 11 -1)
stp x29, x30, [sp, #504]|(KEYWORD::STP 29 30 31 504)
ldp x19, x20, [sp, #-512]|(KEYWORD::LDP 19 20 31 -512)
ldp x29, x30, [sp], #16|(KEYWORD::LDP-POST 29 30 31 16)
stp x29, x30, [sp, #-16]!|(KEYWORD::STP-PRE 29 30 31 -16)
b Lend|(KEYWORD::B "end")
bl Lstart|(KEYWORD::BL "start")
b.ne Lstart|(KEYWORD::B-COND KEYWORD::NE "start")
cbz x0, Lend|(KEYWORD::CBZ 0 "end")
cbnz x2, Lstart|(KEYWORD::CBNZ 2 "start")
tbz w3, #5, Lend|(KEYWORD::TBZ 3 5 "end")
tbnz x20, #63, Lstart|(KEYWORD::TBNZ 20 63 "start")
adr x7, Lend|(KEYWORD::ADR 7 "end")
adrp x9, 0; add x9, x9, #0|(KEYWORD::ADR-FAR 9 "start")
Lend:|(KEYWORD::LABEL "end")
br x9|(KEYWORD::BR 9)
blr x9|(KEYWORD::BLR 9)
ret|(KEYWORD::RET)
svc #65535|(KEYWORD::SVC 65535)
.quad -16909060|(KEYWORD::QUAD -16909060)
EXAMPLES

{
    printf '.text\n'
    awk -F '|' '{ gsub(/; */, "\n", $1); print $1 }' "$dir/examples"
    printf '.ascii "aBc"\n.balign 4, 0\n'
} > "$dir/example.s"
clang -arch arm64 -c "$dir/example.s" -o "$dir/example.o"
otool -s __TEXT __text "$dir/example.o" > "$dir/example.text"

printf 'aBc' > "$dir/payload"
. checker/quote.sh
{
    printf '(BOYMOO-COMPILER::A64-BYTES (BOYMOO-COMPILER::REVERSE-ONTO (COMMON-LISP::QUOTE ('
    awk -F '|' '{ item[NR] = $2 } END { for (i = NR; i > 0; i--) printf "%s%s", (i == NR ? "" : " "), item[i] }' "$dir/examples"
    printf ')) (COMMON-LISP::CONS (COMMON-LISP::CONS (COMMON-LISP::QUOTE KEYWORD::BYTES) (COMMON-LISP::CONS '
    quote "$dir/payload"
    printf ' (COMMON-LISP::QUOTE COMMON-LISP::NIL))) (COMMON-LISP::QUOTE COMMON-LISP::NIL))))\n'
} > "$dir/example.term"

build/runner/boymoo-run -j -p spec/ground.txt -p "$dir/compiler.statements" \
    "$dir/ground.program" "$dir/library.statements" \
    "$dir/compiler.program" < "$dir/example.term" > "$dir/example.string"

awk '
    function byte(s, first, second) {
        first = index("0123456789abcdef", tolower(substr(s, 1, 1))) - 1
        second = index("0123456789abcdef", tolower(substr(s, 2, 1))) - 1
        if (first < 0 || second < 0) exit 1
        printf "%c", first * 16 + second
    }
    NR > 2 {
        for (i = 2; i <= NF; i++) {
            if (length($i) != 8) exit 1
            for (j = 7; j >= 1; j -= 2) byte(substr($i, j, 2))
        }
    }
' "$dir/example.text" > "$dir/assembler.bytes"

awk '
    NR != 1 || /^"/ == 0 || /"$/ == 0 { exit 1 }
    {
        digits = "0123456789ABCDEF"
        for (i = 2; i < length($0); i++) {
            c = substr($0, i, 1)
            if (c != "\\") {
                printf "%s", c
            } else {
                hi = index(digits, substr($0, i + 1, 1)) - 1
                lo = index(digits, substr($0, i + 2, 1)) - 1
                if (i + 2 >= length($0) || hi < 0 || lo < 0) exit 1
                printf "%c", hi * 16 + lo
                i += 2
            }
        }
    }
    END { if (NR != 1) exit 1 }
' "$dir/example.string" > "$dir/compiler.bytes"

cmp "$dir/assembler.bytes" "$dir/compiler.bytes"
printf 'A64 assembler agrees with the system assembler on %d bytes.\n' \
    "$(wc -c < "$dir/compiler.bytes")"
