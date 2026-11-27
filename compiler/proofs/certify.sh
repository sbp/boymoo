#!/bin/sh
# Run from the repository root with ACL2 on PATH.
set -eu

dir=build/compiler/proofs
sources=compiler/proofs
compiler_books='a64 read index data resolve simplify qir rt-qir lower expand opt abi isel rega emit runtime'
set -- values l1 l1-well-formed word-ops heap qir-semantics word-properties rt-semantics rt-length-list \
    mir-semantics rega-check p0 p1 p2 p3 p4 p5 p5-licm p6 p6-clears p6-forward p7 p8 p9

# The compiler build copies and certifies the compiler books in dependency order.
sh compiler/build.sh -d "$dir" $compiler_books
acl=$dir/acl2
model=$dir/compiler/model
proofs=$acl/proofs
mkdir -p "$model" "$proofs"
TMPDIR=$(pwd -P)/$dir/tmp
export TMPDIR

copy() {
    if ! cmp -s "$1" "$2"; then
        cp "$1" "$2"
    fi
}

certify() {
    cert_dir=$1
    cert_book=$2
    cert_version=$3
    shift 3
    if ! (cd "$cert_dir" && {
        printf '(ld "%s")\n' "$cert_version"
        for package_file in "$@"; do
            printf '(ld "%s")\n' "$package_file"
        done
        printf '(certify-book "%s" %s nil :skip-proofs-okp nil :defaxioms-okp nil :ttags nil)\n' \
            "$cert_book" "$#"
        printf '(good-bye)\n'
    } | acl2 > "$cert_book.out" 2>&1) || [ ! -s "$cert_dir/$cert_book.cert" ] ||
        grep -Eq 'ACL2 Error|\*\*\*\*\*\*\*\* FAILED' "$cert_dir/$cert_book.out"; then
        printf 'ACL2 did not certify %s. See %s/%s.out.\n' "$cert_book" "$cert_dir" "$cert_book" >&2
        exit 1
    fi
    printf 'Certified %s.\n' "$cert_book"
}

copy checks/version.lsp "$dir/version.lsp"
copy compiler/model/package.lsp "$model/package.lsp"
model_stale=0
for book in core a64-state a64-decode a64; do
    copy "compiler/model/$book.lisp" "$model/$book.lisp"
    if [ "$model_stale" -eq 1 ] || [ ! -s "$model/$book.cert" ] ||
        [ "$model/$book.lisp" -nt "$model/$book.cert" ] ||
        [ "$model/package.lsp" -nt "$model/$book.cert" ] ||
        [ "$dir/version.lsp" -nt "$model/$book.cert" ]; then
        rm -f "$model/$book.cert"
        certify "$model" "$book" ../../version.lsp package.lsp
        model_stale=1
    fi
done

stale=0
for book in "$@"; do
    case $book in
        ''|*[!a-z0-9-]*) printf 'Invalid proof book name: %s\n' "$book" >&2; exit 2 ;;
    esac
    copy "$sources/$book.lisp" "$proofs/$book.lisp"
    if [ ! -s "$proofs/$book.cert" ] || [ "$proofs/$book.lisp" -nt "$proofs/$book.cert" ] ||
        [ "$dir/version.lsp" -nt "$proofs/$book.cert" ]; then
        stale=1
    fi
    for dependency in "$acl"/*.cert "$model"/*.cert; do
        if [ "$dependency" -nt "$proofs/$book.cert" ]; then
            stale=1
        fi
    done
    if [ "$stale" -eq 1 ]; then
        rm -f "$proofs/$book.cert"
        certify "$proofs" "$book" ../../version.lsp ../package.lsp ../../compiler/model/package.lsp
    fi
done
printf 'ACL2 certificates are up to date in %s.\n' "$proofs"
