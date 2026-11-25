#!/bin/sh
# Run this command from the root of the repository.
set -eu
export LC_ALL=C

if [ "$#" -gt 1 ] || { [ "$#" -eq 1 ] && [ "$1" != --certify-only ]; }; then
    printf '%s\n' 'Usage: sh compiler/model/a64-test.sh [--certify-only]' >&2
    exit 2
fi

mkdir -p build/compiler/a64-model
dir=$(mktemp -d build/compiler/a64-model/test.XXXXXX)
export TMPDIR="$PWD/$dir"

certify() {
    work=$1
    shift
    for book do
        (cd "$work" &&
            printf '(ld "version.lsp")\n(ld "package.lsp")\n(certify-book "%s" 1 nil :skip-proofs-okp nil :defaxioms-okp nil :ttags nil)\n(good-bye)\n' "$book" |
            timeout 10 acl2 > "$book.out" 2>&1)
        if [ ! -s "$work/$book.cert" ]; then
            printf 'Certification failed. See %s/%s.out.\n' "$work" "$book" >&2
            exit 1
        fi
    done
}

mkdir "$dir/model"
cp checks/version.lsp compiler/model/package.lsp compiler/model/a64-state.lisp \
    compiler/model/a64-decode.lisp compiler/model/a64.lisp "$dir/model/"
certify "$dir/model" a64-state a64-decode a64
printf '%s\n' 'ACL2 certified a64-state, a64-decode and a64.'

if [ "$#" -eq 0 ]; then
    runner=build/runner/boymoo-run
    library=build/export/library.statements
    test -x "$runner"
    test -s "$library"
    mkdir "$dir/image"
    cp checks/version.lsp compiler/package.lsp compiler/a64.lisp compiler/sha256.lisp \
        compiler/macos.lisp compiler/model/a64-test-image.lisp "$dir/image/"
    certify "$dir/image" a64 sha256 macos a64-test-image
    timeout 15 sh export/book.sh "$dir/image/a64-test-image"
    exported=build/export/books/$dir/image/a64-test-image
    test -s "$exported.readback"
    awk '{ n = $NF; sub(/\)$/, "", n); if ($(NF - 1) != n) exit 1 }' "$exported.readback"
    grep '^(define ' spec/ground.txt > "$dir/ground.program"
    awk -f checker/library.awk spec/ground.txt "$exported.statements" "$library" \
        > "$dir/library.program"

    printf '%s\n' '(BOYMOO-COMPILER::A64-TEST-IMAGE)' |
        timeout 10 env time -p "$runner" -v -j -m 128 -p spec/ground.txt \
            -p "$exported.statements" "$dir/ground.program" "$dir/library.program" \
            "$exported.program" > "$dir/image.string" 2> "$dir/runner.out"
    cat "$dir/runner.out"

    . compiler/decode.sh
    if ! decode_string "$dir/image.string" > "$dir/cases"; then
        printf '%s\n' 'The reference runner did not print a byte string.' >&2
        exit 1
    fi
    chmod +x "$dir/cases"

    timeout 5 "$dir/cases" > "$dir/stdout"
    {
        printf "(assert-event (boymoo-model::a64-test-compare '("
        # Reverse the bytes of each word for ACL2 hexadecimal notation.
        # Keeping the digits as text preserves every bit.
        if ! od -A n -v -t x1 "$dir/stdout" | awk '
            {
                for (i = 1; i <= NF; i++) {
                    word = $i word
                    if (++bytes % 8 == 0) {
                        printf " #x%s", word
                        word = ""
                    }
                }
            }
            END { if (bytes < 16 || bytes % 8) exit 1 }
        '; then
            printf '%s\n' 'The processor output does not contain whole words and an address header.' >&2
            exit 1
        fi
        printf ')))\n'
        printf '%s\n' '(cw "A64 processor and ACL2 agree in ~x0 cases.~%"' \
            '    (len boymoo-compiler::*a64-test-cases*))'
    } > "$dir/observed.lsp"
fi

{
    printf '(ld "checks/version.lsp")\n(ld "compiler/model/package.lsp")\n'
    printf '(include-book "%s/model/a64")\n' "$dir"
    printf '(ld "compiler/model/a64-test.lsp" :ld-error-action :error)\n'
    if [ "$#" -eq 0 ]; then
        printf '(ld "compiler/package.lsp")\n'
        printf '(include-book "%s/image/a64-test-image")\n' "$dir"
        printf '(ld "compiler/model/a64-test-compare.lsp" :ld-error-action :error)\n'
        printf '(ld "%s/observed.lsp" :ld-error-action :error)\n' "$dir"
    fi
    printf '(good-bye)\n'
} | timeout 10 acl2 > "$dir/test.out" 2>&1
if ! grep -Fq 'A64 model checks passed.' "$dir/test.out"; then
    printf 'A64 model checks failed. See %s/test.out.\n' "$dir" >&2
    exit 1
fi
printf '%s\n' 'A64 model checks passed.'
if [ "$#" -eq 0 ] &&
   ! grep -oE 'A64 processor and ACL2 agree in [0-9]+ cases\.' "$dir/test.out"; then
    printf 'A64 processor comparison failed. See %s/test.out.\n' "$dir" >&2
    exit 1
fi
