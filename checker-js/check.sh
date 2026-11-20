#!/bin/sh
set -eu

if [ "$#" -lt 3 ] || [ "$#" -gt 4 ]; then
    printf '%s\n' 'Usage: sh checker-js/check.sh LIBRARY STATEMENTS PROOFS [ENGINE]' >&2
    exit 2
fi
engine=${4:-${BOYMOO_ENGINE:-}}
if [ -z "$engine" ]; then
    for candidate in node duk qjs jsc; do
        if engine=$(command -v "$candidate"); then
            break
        fi
    done
fi
if [ -z "$engine" ]; then
    printf '%s\n' 'No JavaScript engine found on PATH' >&2
    exit 2
fi
case ${engine##*/} in
    node|node[0-9]*) exec "$engine" checker-js/check-node.js "$1" "$2" "$3" ;;
    jsc|jsc[0-9]*) exec "$engine" checker-js/check.js checker-js/check-jsc.js -- spec/ground.txt "$1" "$2" "$3" ;;
esac

export LC_ALL=C
mkdir -p build
scratch=$(mktemp -d build/checker-js-input.XXXXXX)
trap 'rm -rf "$scratch"' 0
trap 'exit 2' HUP INT TERM
{
    printf '%s\n' 'var boymooInputs = [];'
    for source in spec/ground.txt "$1" "$2" "$3"; do
        od -A n -t x1 -v < "$source" > "$scratch/bytes"
        awk -f checker-js/encode.awk "$scratch/bytes"
    done
} > "$scratch/inputs.js"
cat checker-js/check.js "$scratch/inputs.js" checker-js/check-shell.js > "$scratch/run.js"
"$engine" "$scratch/run.js"
