#!/bin/sh
# Run from the root of the repository.
set -eu

mkdir -p build/compiler/core
dir=build/compiler/core/test.$(date +%Y%m%d%H%M%S).$$
mkdir "$dir"
TMPDIR=$(pwd -P)/$dir
export TMPDIR

make -f runner/Makefile > "$dir/make.out"
cp compiler/model/core.lisp compiler/model/package.lsp \
   compiler/model/core-test.lsp checks/version.lsp checks/canon.lisp \
   checks/canon.lsp "$dir/"

cat > "$dir/test.program" <<'PROGRAM'
(define COMMON-LISP::NIL (ACL2::CORE-LOOP (ACL2::N ACL2::ACC) (COMMON-LISP::IF (COMMON-LISP::< (COMMON-LISP::QUOTE 0) ACL2::N) (ACL2::CORE-LOOP (ACL2::BINARY-+ (COMMON-LISP::QUOTE -1) ACL2::N) (ACL2::BINARY-+ (COMMON-LISP::QUOTE 1) ACL2::ACC)) ACL2::ACC)))
(define COMMON-LISP::NIL (ACL2::CORE-PLUS-ONE (ACL2::X) ((COMMON-LISP::LAMBDA (ACL2::Y) (ACL2::BINARY-+ ACL2::Y (COMMON-LISP::QUOTE 1))) ACL2::X)))
(define COMMON-LISP::NIL (ACL2::CORE-REDEFINED (ACL2::X) (COMMON-LISP::QUOTE 0)))
(define COMMON-LISP::NIL (ACL2::CORE-REDEFINED (ACL2::X) ACL2::X))
(define COMMON-LISP::NIL (ACL2::CORE-MBE (ACL2::X) (ACL2::RETURN-LAST (COMMON-LISP::QUOTE ACL2::MBE1-RAW) (ACL2::CORE-UNDEFINED ACL2::X) ACL2::X)))
(define COMMON-LISP::NIL (COMMON-LISP::LENGTH (ACL2::X) (COMMON-LISP::QUOTE 999)))
(attach ACL2::CORE-ATTACHED ACL2::CORE-UNDEFINED)
(attach ACL2::CORE-ATTACHED ACL2::CORE-ALIAS)
(attach ACL2::CORE-ALIAS ACL2::CORE-PLUS-ONE)
(attach ACL2::CORE-LENGTH COMMON-LISP::LENGTH)
PROGRAM

cat > "$dir/test.packages" <<'PACKAGES'
(package "BOYMOO-CORE-VISIBLE" (COMMON-LISP::CAR))
(hidden-package "BOYMOO-CORE-HIDDEN" (COMMON-LISP::CAR))
PACKAGES

cat > "$dir/values.terms" <<'TERMS'
(ACL2::CORE-LOOP (COMMON-LISP::QUOTE 3) (COMMON-LISP::QUOTE 4))
(ACL2::CORE-ATTACHED (COMMON-LISP::QUOTE 7))
(ACL2::CORE-REDEFINED (COMMON-LISP::QUOTE 9))
(ACL2::CORE-MBE (COMMON-LISP::QUOTE 17))
(COMMON-LISP::CAR (COMMON-LISP::QUOTE 7))
(ACL2::BAD-ATOM<= (COMMON-LISP::QUOTE 1) (COMMON-LISP::QUOTE 2))
(COMMON-LISP::ASH (COMMON-LISP::QUOTE 0) (COMMON-LISP::QUOTE 100000000000000000000))
(ACL2::BINARY-LOGXOR (COMMON-LISP::QUOTE -2) (COMMON-LISP::QUOTE 3))
(ACL2::CORE-LENGTH (COMMON-LISP::QUOTE (1 . 2)))
(COMMON-LISP::CHAR (COMMON-LISP::QUOTE "ab") (COMMON-LISP::QUOTE -1))
(COMMON-LISP::SUBSEQ (COMMON-LISP::QUOTE (1 . 2)) (COMMON-LISP::QUOTE 18446744073709551616) (COMMON-LISP::QUOTE COMMON-LISP::NIL))
(ACL2::PKG-IMPORTS (COMMON-LISP::QUOTE "BOYMOO-CORE-VISIBLE"))
(ACL2::INTERN-IN-PACKAGE-OF-SYMBOL (COMMON-LISP::QUOTE "CAR") (COMMON-LISP::QUOTE BOYMOO-CORE-HIDDEN::X))
TERMS

cat > "$dir/stops.terms" <<'TERMS'
(ACL2::CORE-UNDEFINED (COMMON-LISP::QUOTE 1))
(ACL2::PKG-WITNESS (COMMON-LISP::QUOTE ""))
(ACL2::PKG-IMPORTS (COMMON-LISP::QUOTE "BOYMOO-CORE-HIDDEN"))
(ACL2::SYMBOL-PACKAGE-NAME (COMMON-LISP::QUOTE BOYMOO-CORE-HIDDEN::X))
TERMS

cat "$dir/values.terms" "$dir/stops.terms" > "$dir/queries.terms"

if ! (cd "$dir" && acl2 > acl2.out 2>&1 <<'ACL2'
(ld "version.lsp")
(ld "package.lsp")
(certify-book "core" 1 nil :skip-proofs-okp nil :defaxioms-okp nil :ttags nil)
(include-book "core")
(ld "canon.lsp")
(ld "core-test.lsp")
(good-bye)
ACL2
) || [ ! -s "$dir/core.cert" ] || [ ! -s "$dir/model.results" ] ||
    grep -Eq 'ACL2 Error|\*\*\*\*\*\*\*\* FAILED' "$dir/acl2.out"; then
    printf 'ACL2 certification or evaluation failed. See %s/acl2.out.\n' "$dir" >&2
    exit 1
fi
printf 'ACL2 8.7 certified core.lisp in logic mode.\n'

run() {
    build/runner/boymoo-run -j -m 32 -p spec/ground.txt \
        -p "$dir/test.packages" "$dir/test.program"
}

run < "$dir/values.terms" > "$dir/runner.results"
while IFS= read -r term; do
    status=0
    printf '%s\n' "$term" | run > "$dir/stop.out" 2> "$dir/stop.err" || status=$?
    if [ "$status" -ne 1 ] || [ -s "$dir/stop.out" ] ||
        ! grep -q 'no value:' "$dir/stop.err"; then
        printf 'Unexpected runner stop (status %s) for %s\n' "$status" "$term" >&2
        cat "$dir/stop.err" >&2
        exit 1
    fi
    printf 'KEYWORD::NO-VALUE\n' >> "$dir/runner.results"
done < "$dir/stops.terms"

diff -u "$dir/runner.results" "$dir/model.results"
values=$(grep -c . "$dir/values.terms")
stops=$(grep -c . "$dir/stops.terms")
printf '%s values and %s no-value stops agree with boymoo-run -j.\n' "$values" "$stops"
printf 'The model distinguishes fuel exhaustion from a value of NIL.\n'
printf 'The certificate, log and results are in %s.\n' "$dir"
