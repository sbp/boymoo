#!/bin/sh
# Prove books and have both checkers judge them from the repository root.
set -u
export LC_ALL=C
set -f

usage() {
    printf '%s\n' 'Usage: sh prover/books.sh [-j JOBS] [-t SECONDS] [-f | -l LIBRARY-PROOFS] BOOK ...' \
        '       sh prover/books.sh [-j JOBS] [-t SECONDS] [-f | -l LIBRARY-PROOFS] --all' \
        '       sh prover/books.sh --summary' >&2
    exit 2
}

fail() {
    printf 'prover/books.sh: %s\n' "$*" >&2
    exit 2
}

driver=${PROVER_DRIVER:-fast}
library=build/export/library.statements
case $driver in
    fast) work=build/prover/books; default_proofs=build/prover/library.proofs ;;
    compiled) work=build/prover/books-compiled; default_proofs=build/prover/library-compiled.proofs ;;
    *) fail 'PROVER_DRIVER must be fast or compiled.' ;;
esac

run_bounded() {
    if [ -n "$seconds" ]; then timeout -k 5 "$seconds" "$@"; else "$@"; fi
}

stop_reason() {
    case $1 in
        3) printf 'exhausted memory (status 3)' ;;
        124) printf 'reached its time limit (status 124)' ;;
        *) printf 'stopped with status %s' "$1" ;;
    esac
}

record_book() {
    if [ ! -f "$statements" ] || [ ! -r "$statements" ]; then
        printf 'unavailable\nNo readable statements file at %s.\n' "$statements"
        return
    fi
    set -- "$library" "$statements"
    if [ -f "$aids" ]; then set -- "$@" "$aids"; fi
    run_bounded sh prover/driver/prove.sh "$@" > "$base.raw" 2> "$base.driver-errors"
    status=$?
    if [ "$status" -ne 0 ]; then
        printf 'unresolved\nThe driver %s. All obligations remain.\n' "$(stop_reason "$status")"
        return
    fi
    known=$work/library-helpers
    [ -f "$known" ] || known=$library_proofs
    if ! awk -v known="$known" -f prover/tools/repeats.awk "$base.raw" > "$base.proofs"; then
        printf 'unresolved\nCould not assemble the proof file. All obligations remain.\n'
        rm -f "$base.proofs"
        return
    fi
    rm -f "$base.raw"

    set -- "$library" "$statements" "$base.proofs" "$library_proofs"
    if [ "$driver" = compiled ]; then
        run_bounded sh compiler/check.sh "$@" > "$base.core" 2> "$base.core-errors"
    else
        run_bounded env RUNNER=build/runner-fast/boymoo-run-fast sh checker/check.sh "$@" \
            > "$base.core" 2> "$base.core-errors"
    fi
    status=$?
    core=
    if [ "$status" -ne 0 ]; then core_report=$(stop_reason "$status")
    elif IFS= read -r core < "$base.core"; then core_report="gave $core"
    else core=; core_report='wrote no verdict'; fi
    run_bounded sh checker-js/check.sh "$@" node > "$base.second" 2> "$base.second-errors"
    status=$?
    second=
    if [ "$status" -ne 0 ]; then second_report=$(stop_reason "$status")
    elif IFS= read -r second < "$base.second"; then second_report="gave $second"
    else second=; second_report='wrote no verdict'; fi

    if [ "$core" = accepted ] && [ "$second" = accepted ]; then
        printf 'accepted\n'
    else
        printf 'unresolved\n'
    fi
    printf 'The ACL2 Core checker %s. The JavaScript checker %s.\n' "$core_report" "$second_report"
    awk '/^\(skip / { print "Unproved obligation " substr($0, 7, length($0) - 7) "." }' "$base.proofs"
}

prove_book() {
    book=$1
    statements=build/export/books/$book.statements
    aids=build/export/books/$book.aids
    base=$work/$book
    mkdir -p "$(dirname "$base")" || exit 2
    rm -f "$base.proofs"
    trap 'rm -f "$base.raw" "$base.result.tmp"; exit 2' HUP INT TERM
    record_book > "$base.result.tmp" || exit 2
    mv "$base.result.tmp" "$base.result" || exit 2
    rm -f "$base.raw"
}

if [ "${1-}" = --prove-book ]; then
    [ "$#" -eq 4 ] || [ "$#" -eq 5 ] || usage
    [ "$#" -eq 5 ] || exit 0
    if [ "$2" = 1 ]; then work=$work/all; fi
    library_proofs=$3 seconds=$4
    prove_book "$5"
    exit
fi

book_names() {
    sed 's/#.*//; s/^[[:space:]]*//; s/[[:space:]]*$//; /^$/d' export/books.txt
}

book_state() {
    if [ -s "$work/$1.result" ]; then
        IFS= read -r state < "$work/$1.result"
    else
        state=pending
    fi
}

summarize() {
    printf '%s\n' "$@" | awk -v work="$work" '
        BEGIN { print "Books accepted in full by both checkers" }
        {
            file = work "/" $0 ".result"
            if ((getline state < file) <= 0) {
                other[++lines] = $0 " has no completed attempt."
            } else {
                tried++
                if (state == "accepted") {
                    print "  " $0
                    accepted++
                } else {
                    other[++lines] = $0
                    while ((getline detail < file) > 0) other[++lines] = "  " detail
                }
            }
            close(file)
        }
        END {
            print "Other books"
            for (i = 1; i <= lines; i++) print other[i]
            printf "Accepted %d of %d books tried. The list has %d books, with %d pending.\n",
                   accepted, tried, NR, NR - tried
            exit (accepted != NR)
        }'
}

fresh=
library_proofs=
jobs=1
seconds=
all=0
summary=0
while [ "$#" -gt 0 ]; do
    case $1 in
        -f) fresh=-f; shift ;;
        -l) [ "$#" -ge 2 ] || usage; library_proofs=$2; shift 2 ;;
        -j) [ "$#" -ge 2 ] || usage; jobs=$2; shift 2 ;;
        -t) [ "$#" -ge 2 ] || usage; seconds=$2; shift 2 ;;
        --all) all=1; shift ;;
        --summary) summary=1; shift ;;
        --) shift; break ;;
        -*) usage ;;
        *) break ;;
    esac
done
case $jobs in ''|0*|*[!0-9]*) usage ;; esac
case ${seconds:-1} in 0*|*[!0-9]*) usage ;; esac
[ -z "$fresh" ] || [ -z "$library_proofs" ] || usage

if [ "$all" -eq 1 ] || [ "$summary" -eq 1 ]; then
    [ "$#" -eq 0 ] || usage
    work=$work/all
    seconds=${seconds:-600}
    names=$(book_names) || exit 2
    set -- $names
fi
[ "$#" -ge 1 ] || usage
for book do
    case /$book/ in //*|*/../*) fail "invalid book name $book" ;; esac
done
if [ "$summary" -eq 1 ]; then
    summarize "$@"
    exit
fi

if [ "$driver" = compiled ]; then
    [ -x build/compiler/prover ] || fail 'Run sh compiler/build-prover.sh first.'
    [ -x build/compiler/checker ] || fail 'Run sh compiler/build-checker.sh first.'
fi
mkdir -p "$work" || exit 2
mkdir "$work/lock" || fail "another run holds $work/lock"
trap 'rmdir "$work/lock"' 0
trap 'exit 2' HUP INT TERM

if [ -z "$library_proofs" ]; then
    library_proofs=$default_proofs
    sh prover/library.sh -j "$jobs" $fresh "$library_proofs" > "$work/library.out" || {
        cat "$work/library.out"
        fail 'The library proof command failed.'
    }
    cat "$work/library.out"
    grep -q '; 0 left as skips;' "$work/library.out" || fail 'The library has unproved obligations.'
fi
[ -s "$library_proofs" ] || fail "no file $library_proofs"
[ -s "$library" ] || fail "no file $library"

# repeats.awk needs the helper head lines of the library's proofs.
awk '/^\((define|lemma|choose) /' "$library_proofs" > "$work/library-helpers.tmp" || exit 2
mv "$work/library-helpers.tmp" "$work/library-helpers" || exit 2

for book do rm -f "$work/$book.result"; done
start=$(date +%s)
printf '%s\000' "$@" |
    xargs -0 -P "$jobs" -n 1 sh prover/books.sh --prove-book "$all" "$library_proofs" "$seconds" || exit 2

if [ "$all" -eq 1 ]; then
    printf 'Book attempts took %s seconds.\n' "$(($(date +%s) - start))"
    summarize "$@"
    exit
fi

failed=0
for book do
    book_state "$book"
    printf '%s\n' "$book"
    sed '1d; s/^/  /' "$work/$book.result"
    [ "$state" = accepted ] || failed=1
done
if [ "$failed" -eq 0 ]; then
    printf 'All %s books accepted by both checkers.\n' "$#"
else
    printf '%s\n' 'Some books have no proof accepted by both checkers.'
    exit 1
fi
