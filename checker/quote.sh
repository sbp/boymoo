# Shell functions for checker/check.sh and checker/books.sh, which read
# this file with the command ".".

# Writes, as a quoted constant, the string whose characters are the bytes
# of the file $1, in the text of spec/formats.md, section 2: a byte from 32
# to 126 other than " and \ is written as itself, and any other as \ and
# two hexadecimal digits.  A file that holds only bytes from 32 to 126 and
# line feeds, as every file in the format does (spec/formats.md, section 1),
# is written a line at a time: sed writes \ and " as \5C and \22, and awk
# writes \0A for each line feed, which needs a sed and an awk that take
# lines of any length.  Any other file is written a byte at a time, from od.
quote() {
    printf '(COMMON-LISP::QUOTE "'
    if [ "$(LC_ALL=C tr -d ' -~\n' < "$1" | wc -c)" -eq 0 ]; then
        last=$(tail -c 1 "$1" | od -A n -t u1 | tr -d ' ')
        LC_ALL=C sed -e 's/\\/\\5C/g' -e 's/"/\\22/g' "$1" |
            LC_ALL=C awk -v last="$last" '{ printf "%s%s", (NR > 1 ? "\\0A" : ""), $0 }
                                          END { if (last == 10) printf "\\0A" }'
    else
        od -A n -v -t u1 "$1" |
            awk '{ for (i = 1; i <= NF; i++) {
                       c = $i + 0
                       if (c >= 32 && c <= 126 && c != 34 && c != 92) printf "%c", c
                       else printf "\\%02X", c } }'
    fi
    printf '")'
}

# Runs CHECK-FOUR on the runner $RUNNER, from the program text of the
# ground theory, of the checker's library and of the checker, with the
# runner's prelude (-j, runner/README.md), which computes length and char
# itself: the checker reads each input by position with them
# (string-lines, checker/check.lisp). The quoted constants are files for
# spec/ground.txt, the library, the statements, the proofs and the
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
          "$RUNNER" -j -p spec/ground.txt -p build/checker/checker.statements \
              build/checker/ground.program build/checker/library.statements \
              build/checker/checker.program)
    status=$?
    if [ $status -ne 0 ]; then
        echo "the runner stopped with status $status"
        return $status
    fi
    # The two strings hold no " and no \.
    printf '%s\n' "$out" | sed -n 's/^("\([^"]*\)" "\([^"]*\)")$/\1\
\2/p'
}
