#!/bin/sh
# Read the input files and print the proof text.
set -eu
export LC_ALL=C
set -f

usage() {
    printf '%s\n' \
        'usage: sh prover/driver/prove.sh [--sets A,B] [--ranks N] [--checked] LIBRARY STATEMENTS [AIDS]' >&2
    exit 2
}

sets=
ranks=
checked=0
while [ "$#" -gt 0 ]; do
    case $1 in
        --sets)
            [ "$#" -ge 2 ] || usage
            case $2 in ''|,*|*,|*,,*) usage ;; esac
            sets=KEYWORD::SETS
            seen=' '
            old_ifs=$IFS
            IFS=,
            for name in $2; do
                case $name in T1|T2|T3|T4|H1|H2|H3|H4|B1|B2|L1) ;; *) usage ;; esac
                case $seen in *" $name "*) usage ;; esac
                seen="$seen$name "
                sets="$sets \"$name\""
            done
            IFS=$old_ifs
            sets="($sets)"
            shift 2 ;;
        --ranks)
            [ "$#" -ge 2 ] || usage
            case $2 in ''|*[!0-9]*) usage ;; esac
            limit=$2
            while [ "${limit#0}" != "$limit" ]; do limit=${limit#0}; done
            ranks="(KEYWORD::RANKS . ${limit:-0})"
            shift 2 ;;
        --checked) checked=1; shift ;;
        --) shift; break ;;
        -*) usage ;;
        *) break ;;
    esac
done
[ "$#" -eq 2 ] || [ "$#" -eq 3 ] || usage
for file do
    if [ ! -f "$file" ] || [ ! -r "$file" ]; then
        printf 'prover/driver/prove.sh: cannot read %s\n' "$file" >&2
        exit 2
    fi
done

if [ -n "$sets" ] && [ -n "$ranks" ]; then
    options="($sets $ranks)"
elif [ -n "$sets$ranks" ]; then
    options="($sets$ranks)"
else
    options=COMMON-LISP::NIL
fi

. checker/quote.sh
quote_input() {
    case $1 in -*) quote "./$1" ;; *) quote "$1" ;; esac
}

work=build/prover/driver
scratch=$work/prove.$$
mkdir -p "$work"
mkdir "$scratch"
trap 'rm -rf "$scratch"' 0
trap 'exit 2' HUP INT TERM
{
    if [ "$checked" -eq 1 ]; then
        printf '(BOYMOO-PROVER::DRIVER-PROVE-CHECKED '
        quote spec/ground.txt
        printf ' '
    else
        printf '(BOYMOO-PROVER::DRIVER-PROVE '
    fi
    quote_input "$1"
    printf ' '
    quote_input "$2"
    printf ' '
    if [ "$#" -eq 3 ]; then quote_input "$3"; else printf '(COMMON-LISP::QUOTE "")'; fi
    printf ' (COMMON-LISP::QUOTE %s))\n' "$options"
} > "$scratch/term"

if [ "${PROVER_DRIVER_VERBOSE-}" = 1 ]; then
    set -- -v
else
    set --
fi
sh prover/driver/run.sh "$@" < "$scratch/term" > "$scratch/value"
if ! awk -v checked="$checked" -v diagnostic="$scratch/error" \
        -f prover/driver/unquote.awk "$scratch/value"; then
    printf 'prover/driver/prove.sh: ' >&2
    cat "$scratch/error" >&2
    exit 1
fi
