#!/bin/sh
set -eu

# Run from the repository root. The optional argument limits the number of
# exported books checked on the reference runner. Both programs check every
# case that has a verdict file.
book_references=${1:-20}
case $book_references in
    *[!0-9]*) echo 'Usage: sh compiler/test-checker.sh [BOOK-REFERENCES]' >&2; exit 2 ;;
esac
if [ "$#" -gt 1 ]; then
    echo 'Usage: sh compiler/test-checker.sh [BOOK-REFERENCES]' >&2
    exit 2
fi

runner=build/runner/boymoo-run
if [ ! -x "$runner" ]; then
    echo "compiler/test-checker.sh requires $runner" >&2
    exit 2
fi

export LC_ALL=C
work=build/compiler/checker-test
mkdir -p "$work/tmp"
export TMPDIR="$PWD/$work/tmp"

sh compiler/build-checker.sh

. checker/quote.sh
. compiler/frame.sh

# Exported statements use the canonical text in spec/formats.md.
# A definition needs a skip when one of its bodies calls a function in
# the group outside a quotation or the executable half of an mbe.
write_skips() {
    awk '
    function tokenize(line,    count, depth, open, first, end, i, c, delimiter) {
        end = length(line)
        for (i = 1; i <= end; i++) {
            c = substr(line, i, 1)
            if (c == " ") continue
            if (c == "(") {
                token[++count] = c
                open[++depth] = count
            } else if (c == ")") {
                token[++count] = c
                after[open[depth--]] = count + 1
                after[count] = count + 1
            } else {
                first = i
                delimiter = ""
                if (substr(line, i, 3) == "#C(") {
                    delimiter = ")"
                    i += 3
                }
                for (; i <= end; i++) {
                    c = substr(line, i, 1)
                    if (delimiter != "") {
                        if (c == delimiter) delimiter = ""
                    } else if (c == "\"" || c == "|") {
                        delimiter = c
                    } else if (c == " " || c == "(" || c == ")") {
                        break
                    }
                }
                token[++count] = substr(line, first, i - first)
                after[count] = count + 1
                i--
            }
        }
    }
    function calls_defined(first, limit,    i, op, arg, logical) {
        for (i = first; i < limit; i++) {
            if (token[i] != "(") continue
            op = token[i + 1]
            arg = i + 2
            if (op == "COMMON-LISP::QUOTE") {
                i = after[i] - 1
            } else if (op in defined) {
                return 1
            } else if (op == "COMMON-LISP::LAMBDA") {
                i = after[arg] - 1
            } else if (op == "ACL2::RETURN-LAST" &&
                       token[arg] == "(" && token[arg + 1] == "COMMON-LISP::QUOTE" &&
                       token[arg + 2] == "ACL2::MBE1-RAW" && token[arg + 3] == ")") {
                logical = after[after[arg]]
                if (after[logical] == after[i] - 1)
                    i = logical - 1
            }
        }
        return 0
    }
    FILENAME == ARGV[1] { seen[$0] = 1; next }
    !/^\((theorem|define|constrain) / || seen[$0]++ { next }
    {
        tokenize($0)
        name = ""
        if (token[2] == "theorem") {
            name = token[3]
        } else if (token[2] == "constrain") {
            if (token[after[3]] != "COMMON-LISP::NIL") name = token[5]
        } else {
            first = after[3]
            for (key in defined) delete defined[key]
            for (def = first; token[def] == "("; def = after[def])
                defined[token[def + 1]] = 1
            for (def = first; token[def] == "("; def = after[def]) {
                body = after[def + 2]
                if (calls_defined(body, after[body])) {
                    name = token[first + 1]
                    break
                }
            }
        }
        if (name != "") print "(skip " name ")"
    }' "$1" "$2"
}

measure() {
    log=$1
    shift
    # The shell times the command and its children while keeping its
    # report separate from the program standard error.
    zsh -fc 'TIMEFMT="%*E %M"; error=$1; shift; time "$@" 2>"$error"' \
        zsh "$log.err" timeout 15 "$@" > "$log.out" 2> "$log.time"
}

compare() (
    name=$1
    verdict=$2
    paired=$3
    shift 3
    {
        cat "$work/ground.frame"
        for field do frame_field "$field"; done
    } > "$work/frame"
    native_status=0
    measure "$work/native" build/compiler/checker < "$work/frame" || native_status=$?
    read -r native_time native_rss < "$work/native.time"

    : > "$work/expected"
    if [ -n "$verdict" ]; then
        IFS= read -r expected < "$verdict" || :
        printf '%s\n' "$expected" > "$work/expected"
    fi
    : > "$work/reference.verdict"
    : > "$work/reference.err"
    reference_status=
    reference_time=0
    reference_rss=0
    reference_match=0
    agreed=0
    if [ "$paired" -eq 1 ]; then
        {
            printf '(BOYMOO::CHECK-FOUR '
            cat "$work/ground.quoted"
            for field do
                printf ' '
                if [ -s "$field" ]; then
                    quote "$field"
                else
                    printf '(COMMON-LISP::QUOTE "")'
                fi
            done
            printf ')\n'
        } > "$work/term"
        reference_status=0
        measure "$work/reference" "$runner" -j -p spec/ground.txt \
            -p build/checker/checker.statements build/checker/ground.program \
            build/checker/library.statements build/checker/checker.program \
            < "$work/term" || reference_status=$?
        read -r reference_time reference_rss < "$work/reference.time"
        if [ "$reference_status" -eq 0 ] &&
           ! awk '
            NR == 1 && /^\("[^"]*" "[^"]*"\)$/ {
                verdict = $0
                sub(/^\("/, "", verdict)
                sub(/".*$/, "", verdict)
                found = 1
            }
            END { if (NR != 1 || !found) exit 1; print verdict }
           ' "$work/reference.out" > "$work/reference.verdict"; then
            {
                printf 'The runner returned an unexpected result. '
                cat "$work/reference.out"
            } > "$work/reference.err"
        fi
        if [ -z "$verdict" ]; then
            cp "$work/reference.verdict" "$work/expected"
        fi
        if [ -s "$work/reference.verdict" ]; then
            if cmp -s "$work/reference.verdict" "$work/expected"; then reference_match=1; fi
            if [ "$native_status" -eq 0 ] && cmp -s "$work/native.out" "$work/reference.verdict"; then
                agreed=1
            fi
        fi
    fi
    matched=0
    if [ "$native_status" -eq 0 ] && [ -s "$work/expected" ] &&
       cmp -s "$work/native.out" "$work/expected"; then
        matched=1
    fi

    awk -v name="$name" -v dir="$work" -v native="$native_status" \
        -v reference="$reference_status" '
        function field(file,    line, text) {
            while ((getline line < file) > 0) text = text line "\n"
            close(file)
            sub(/\n+$/, "", text)
            if (text ~ /["\t\n]/) {
                gsub(/"/, "\"\"", text)
                return "\"" text "\""
            }
            return text
        }
        BEGIN {
            OFS = "\t"
            print name, field(dir "/expected"), field(dir "/native.out"), native, \
                field(dir "/native.err"), field(dir "/reference.verdict"), reference, \
                field(dir "/reference.err")
        }' >> "$work/results.tsv"
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$name" "$native_status" "$matched" "$agreed" "$native_time" "$native_rss" \
        "$paired" "$reference_match" "$reference_time" "$reference_rss" >> "$work/times.tsv"
)

run_case() {
    case_dir=$1
    case_verdict=$2
    set --
    for part in library statements proofs library-proofs; do
        field=$case_dir/$part.txt
        if [ ! -f "$field" ]; then field=$work/empty; fi
        set -- "$@" "$field"
    done
    compare "$case_dir" "$case_verdict" 1 "$@"
}

: > "$work/empty"
frame_field spec/ground.txt > "$work/ground.frame"
quote spec/ground.txt > "$work/ground.quoted"
printf 'input\texpected\tcompiled\tcompiled status\tcompiled stderr\treference\treference status\treference stderr\n' \
    > "$work/results.tsv"
: > "$work/times.tsv"
: > "$work/missing-books.txt"
printf 'accepted\n' > "$work/example.verdict"
run_case spec/example "$work/example.verdict"
for root in checker/cases checker-js/cases; do
    for verdict in "$root"/*/verdict.txt; do
        if [ -f "$verdict" ]; then run_case "${verdict%/*}" "$verdict"; fi
    done
done

library=build/export/library.statements
awk '{ sub(/#.*/, ""); sub(/^[[:space:]]+/, ""); sub(/[[:space:]]+$/, ""); if (length) print }' \
    export/books.txt > "$work/books.txt"
books=0
book_pairs=0
missing=0
while IFS= read -r name; do
    statements=build/export/books/$name.statements
    if [ ! -f "$statements" ]; then
        printf '%s\n' "$name" >> "$work/missing-books.txt"
        missing=$((missing + 1))
        continue
    fi
    paired=0
    if [ "$book_pairs" -lt "$book_references" ]; then
        paired=1
        book_pairs=$((book_pairs + 1))
    fi
    write_skips "$library" "$statements" > "$work/book.proofs"
    compare "$name" '' "$paired" "$library" "$statements" "$work/book.proofs" "$work/empty"
    books=$((books + 1))
done < "$work/books.txt"

awk -F '\t' -v books="$books" -v book_pairs="$book_pairs" -v missing="$missing" -v work="$work" '
    # An input fails if the compiled checker stops on it, or if it has a
    # reference run and the compiled verdict, the reference verdict and
    # the expected verdict are not all the same. A book with no reference
    # run has no verdict to compare, and fails only by a stop.
    {
        if ($2 != 0) stops++
        matched += $3
        agreed += $4
        if ($2 != 0 || ($7 && (!$3 || !$4 || !$8))) {
            if (first == "") first = $1
        }
        native_time += $5
        if ($6 > native_rss) native_rss = $6
        if ($7) {
            references++
            reference_matches += $8
            reference_time += $9
            paired_time += $5
            if ($10 > reference_rss) reference_rss = $10
        }
    }
    END {
        printf "Inputs run: %d. Compiled checker matched %d expected verdicts and agreed with the reference runner on %d. Compiled checker stops: %d.\n", NR, matched, agreed, stops
        printf "First input without agreement: %s\n", (first == "" ? "none" : first)
        printf "Compiled checker, all inputs: %.2f s elapsed, %.0f bytes peak RSS.\n", native_time, 1024 * native_rss
        printf "Reference runner matched %d expected verdicts on %d inputs in %.2f s elapsed, %.0f bytes peak RSS.\n", reference_matches, references, reference_time, 1024 * reference_rss
        printf "Compiled checker, same %d inputs: %.2f s elapsed.\n", references, paired_time
        printf "Books run: %d. Books with reference runs: %d. Books missing exports: %d.\n", books, book_pairs, missing
        printf "Results are in %s/results.tsv.\n", work
        exit (first != "" || missing > 0)
    }
' "$work/times.tsv"
