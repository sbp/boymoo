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
set_names=
rank_limit=
checked=0
while [ "$#" -gt 0 ]; do
    case $1 in
        --sets)
            [ "$#" -ge 2 ] || usage
            case $2 in ''|,*|*,|*,,*) usage ;; esac
            set_names=$2
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
            rank_limit=${limit:-0}
            ranks="(KEYWORD::RANKS . $rank_limit)"
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

driver=${PROVER_DRIVER:-fast}
case $driver in
    fast) ;;
    compiled)
        if [ ! -x build/compiler/prover ]; then
            printf '%s\n' 'Run sh compiler/build-prover.sh to build the compiled prover.' >&2
            exit 2
        fi ;;
    *) printf '%s\n' 'PROVER_DRIVER must be fast or compiled.' >&2; exit 2 ;;
esac

work=build/prover/driver
scratch=$work/prove.$$
mkdir -p "$work"
mkdir "$scratch"
trap 'rm -rf "$scratch"' 0
trap 'exit 2' HUP INT TERM

if [ "$driver" = compiled ]; then
    . compiler/frame.sh
    frame_input() {
        case $1 in -*) frame_field "./$1" ;; *) frame_field "$1" ;; esac
    }
    printf '%s' "$set_names" > "$scratch/sets"
    printf '%s' "$rank_limit" > "$scratch/ranks"
    {
        if [ "$checked" -eq 1 ]; then frame_field spec/ground.txt; else printf '\000\000\000\000'; fi
        frame_input "$1"
        frame_input "$2"
        if [ "$#" -eq 3 ]; then frame_input "$3"; else printf '\000\000\000\000'; fi
        frame_field "$scratch/sets"
        frame_field "$scratch/ranks"
    } > "$scratch/frame"
    if [ "${PROVER_DRIVER_VERBOSE-}" = 1 ]; then
        time -p build/compiler/prover < "$scratch/frame"
    else
        build/compiler/prover < "$scratch/frame"
    fi
    exit 0
fi

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
