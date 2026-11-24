# Shell functions for checker/check.sh and checker/books.sh, which read
# this file with the command ".".

# Writes, as a quoted constant, the string whose characters are the bytes
# of the file $1, in the text of spec/formats.md, section 2: a byte from 32
# to 126 other than " and \ is written as itself, and any other as \ and
# two hexadecimal digits.
quote() {
    printf '(COMMON-LISP::QUOTE "'
    od -A n -v -t u1 "$1" |
        awk '{ for (i = 1; i <= NF; i++) {
                   c = $i + 0
                   if (c >= 32 && c <= 126 && c != 34 && c != 92) printf "%c", c
                   else printf "\\%02X", c } }'
    printf '")'
}

# Runs CHECK-FOUR on the runner $RUNNER. The quoted constants are files
# for spec/ground.txt, the library, the statements, the proofs and the
# library's proofs. An omitted fifth file gives an empty string. The two
# output lines give the verdict and a few words on what failed.
run_check() {
    out=$({ printf '(BOYMOO::CHECK-FOUR '
            cat "$1"; printf ' '
            cat "$2"; printf ' '
            cat "$3"; printf ' '
            cat "$4"; printf ' '
            if [ -n "${5-}" ]; then cat "$5"; else printf '(COMMON-LISP::QUOTE "")'; fi
            printf ')\n'; } |
          "$RUNNER" -p spec/ground.txt -p build/checker/checker.statements \
              build/checker/ground.program build/checker/checker.program)
    status=$?
    if [ $status -ne 0 ]; then
        echo "the runner stopped with status $status"
        return $status
    fi
    # The two strings hold no " and no \.
    printf '%s\n' "$out" | sed -n 's/^("\([^"]*\)" "\([^"]*\)")$/\1\
\2/p'
}
