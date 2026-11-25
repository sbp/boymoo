#!/bin/sh
set -eu
export LC_ALL=C

case ${1-} in
    '') compiler=build/compiler/compiler-2 ;;
    --reference) compiler= ;;
    *) printf 'Usage: sh compiler/test-front.sh [--reference]\n' >&2; exit 2 ;;
esac

dir=$(mktemp -d build/compiler/front.XXXXXX)
trap 'rm -rf "$dir"' EXIT
trap 'exit 1' HUP INT TERM

cat > "$dir/quote-formal.program" <<'EOF'
(define COMMON-LISP::NIL (ACL2::MAIN (COMMON-LISP::QUOTE) (COMMON-LISP::CAR (COMMON-LISP::CONS COMMON-LISP::QUOTE (COMMON-LISP::QUOTE "tail")))))
EOF

cat > "$dir/package-repeat.packages" <<'EOF'
(hidden-package "EXAMPLE" (COMMON-LISP::CAR))
(package "EXAMPLE" (COMMON-LISP::CAR))
(package "EXAMPLE" (COMMON-LISP::CAR))
EOF
cat > "$dir/package-repeat.program" <<'EOF'
(define COMMON-LISP::NIL (ACL2::MAIN (ACL2::X) (ACL2::SYMBOL-PACKAGE-NAME (COMMON-LISP::QUOTE EXAMPLE::X))))
EOF

cat > "$dir/undefined-entry.packages" <<'EOF'
(constrain ((ACL2::MAIN 1)) COMMON-LISP::NIL)
EOF
: > "$dir/undefined-entry.program"

cat > "$dir/imported-spelling.program" <<'EOF'
(define COMMON-LISP::NIL (ACL2::MAIN (ACL2::X) (COMMON-LISP::QUOTE ACL2::CAR)))
EOF
cat > "$dir/printable-escape.program" <<'EOF'
(define COMMON-LISP::NIL (ACL2::MAIN (ACL2::X) (COMMON-LISP::QUOTE "a\61")))
EOF
cat > "$dir/duplicate-lambda-formal.program" <<'EOF'
(define COMMON-LISP::NIL (ACL2::MAIN (ACL2::X) ((COMMON-LISP::LAMBDA (ACL2::Y ACL2::Y) ACL2::Y) ACL2::X (COMMON-LISP::QUOTE "second"))))
EOF

check() {
    name=$1
    expected=$2
    packages=$dir/$name.packages
    program=$dir/$name.program
    [ -f "$packages" ] || : > "$packages"

    runner_status=0
    printf '(ACL2::MAIN (COMMON-LISP::QUOTE "correct"))\n' |
        build/runner/boymoo-run -l -j -p spec/ground.txt -p "$packages" "$program" \
            > "$dir/runner.out" 2> "$dir/runner.err" || runner_status=$?
    printf '%s runner status %s\n' "$name" "$runner_status"
    cat "$dir/runner.err"
    [ "$runner_status" -eq "$expected" ]
    if [ "$expected" -eq 2 ]; then
        grep -Fq "$3" "$dir/runner.err"
    fi

    awk '/^\((package|hidden-package) /' spec/ground.txt "$packages" > "$dir/input"
    cat "$program" >> "$dir/input"
    printf '(entry ACL2::MAIN)\n' >> "$dir/input"

    compiler_status=0
    if [ -n "$compiler" ]; then
        "$compiler" < "$dir/input" > "$dir/executable" 2> "$dir/compiler.err" ||
            compiler_status=$?
    else
        sh compiler/compile.sh "$dir/input" > "$dir/executable" 2> "$dir/compiler.err" ||
            compiler_status=$?
    fi
    printf '%s compiler status %s\n' "$name" "$compiler_status"
    cat "$dir/compiler.err"
    if [ "$expected" -eq 2 ]; then
        [ "$compiler_status" -eq 1 ]
        [ ! -s "$dir/executable" ]
        [ ! -s "$dir/runner.out" ]
        return
    fi

    [ "$compiler_status" -eq 0 ]
    chmod +x "$dir/executable"
    executable_status=0
    printf correct | "$dir/executable" > "$dir/executable.out" 2> "$dir/executable.err" ||
        executable_status=$?
    printf '%s executable status %s\n' "$name" "$executable_status"
    cat "$dir/executable.err"
    [ "$executable_status" -eq "$runner_status" ]
    if [ "$expected" -eq 0 ]; then
        {
            printf '"'
            cat "$dir/executable.out"
            printf '"\n'
        } > "$dir/quoted.out"
        cmp "$dir/quoted.out" "$dir/runner.out"
        cat "$dir/runner.out"
    else
        cmp "$dir/executable.out" "$dir/runner.out"
        sed 's/^boymoo-run: standard input, line 1: //' "$dir/runner.err" > "$dir/stop"
        cmp "$dir/executable.err" "$dir/stop"
    fi
}

check quote-formal 0
check package-repeat 0
check undefined-entry 1
check imported-spelling 2 'a symbol that does not exist, since its package imports one of that name'
check printable-escape 2 'a character escaped that is written as itself'
check duplicate-lambda-formal 2 'not a term: ((COMMON-LISP::LAMBDA (ACL2::Y ACL2::Y)'

cat > "$dir/canonical-numbers.program" <<'EOF'
(define COMMON-LISP::NIL (ACL2::MAIN (ACL2::X) (COMMON-LISP::IF (COMMON-LISP::CONSP (COMMON-LISP::QUOTE (0 5 -7 -4611686018427387904 4611686018427387904 1/2 -7/3 1/18446744073709551616 #C(0 -1/2) #C(-7/3 1/18446744073709551616)))) ACL2::X (COMMON-LISP::QUOTE "missing numbers"))))
EOF
check canonical-numbers 0

check_number() {
    printf '(define COMMON-LISP::NIL (ACL2::MAIN (ACL2::X) (COMMON-LISP::QUOTE %s)))\n' \
        "$2" > "$dir/$1.program"
    check "$1" 2 "${3:-a number that is not in its one text}"
}

check_number unreduced-fraction 2/4
check_number whole-fraction 4/2
check_number unit-denominator 1/1
check_number zero-numerator 0/5
check_number negative-zero -0
check_number plus-sign +5
check_number leading-zero 007
check_number negative-leading-zero -007
check_number zero-denominator 1/0
check_number negative-denominator 1/-2
check_number denominator-leading-zero 1/02
check_number missing-numerator /2
check_number missing-denominator 1/
check_number second-slash 1/2/3
check_number complex-zero-imaginary '#C(1 0)' 'not in the format: a complex rational'
check_number complex-unreduced-real '#C(2/4 1)'
check_number complex-unreduced-imaginary '#C(1 2/4)'
check_number complex-extra-space '#C(1  2)'
check_number unreduced-boxed-fraction 18446744073709551616/36893488147419103232
