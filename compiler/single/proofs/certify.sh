#!/bin/sh
# Run from the repository root.
set -eu
export LC_ALL=C

root=compiler/single/proofs
work=build/compiler/single/proofs
foundations='machine kernel loading values heap interfaces checks'

usage() {
    printf '%s\n' 'Usage: sh compiler/single/proofs/certify.sh [--foundations | --books PACKAGE BOOK ...]' >&2
    exit 2
}

name_p() {
    case $1 in
        ''|*[!a-z0-9_-]*) return 1 ;;
        *) return 0 ;;
    esac
}

certify_books() {
    source_dir=$1
    stage_dir=$2
    package_set=$3
    shift 3

    mkdir -p "$stage_dir"
    cp checks/version.lsp "$stage_dir/version.lsp"
    case $package_set in
        model) packages=model ;;
        compiler) packages=compiler ;;
        all) packages='model compiler proofs' ;;
    esac
    portcullis=0
    for book_package in $packages; do
        case $book_package in
            model) package_file=compiler/model/package.lsp ;;
            compiler) package_file=compiler/package.lsp ;;
            proofs) package_file=$root/foundations/package.lsp ;;
        esac
        cp "$package_file" "$stage_dir/$book_package-package.lsp"
        portcullis=$((portcullis + 1))
    done
    for book do
        name_p "$book" || usage
        cp "$source_dir/$book.lisp" "$stage_dir/$book.lisp"
        rm -f "$stage_dir/$book.cert"
        if ! (
            cd "$stage_dir" || exit 1
            {
                printf '%s\n' '(ld "version.lsp")'
                for book_package in $packages; do
                    printf '(ld "%s-package.lsp")\n' "$book_package"
                done
                printf '(certify-book "%s" %s nil :skip-proofs-okp nil :defaxioms-okp nil :ttags nil :pcert nil)\n' "$book" "$portcullis"
                printf '%s\n' '(good-bye)'
            } | acl2 > "$book.out" 2>&1
        ) || [ ! -s "$stage_dir/$book.cert" ]; then
            printf 'ACL2 did not certify %s/%s.lisp. See %s/%s.out.\n' \
                "$source_dir" "$book" "$stage_dir" "$book" >&2
            return 1
        fi
        printf 'Certified %s/%s.lisp.\n' "$source_dir" "$book"
    done
}

certify_foundations() {
    rm -f "$work/foundations.ready"
    # The books of the single-pass compiler, in the order of
    # compiler/single/build.sh: those that both compilers share are in
    # compiler/, and the others in compiler/single/.
    certify_books compiler "$work/compiler" compiler a64 read index data
    certify_books compiler/single "$work/compiler" compiler gen
    certify_books compiler "$work/compiler" compiler sha256 macos linux
    certify_books compiler/single "$work/compiler" compiler runtime compile
    certify_books compiler/model "$work/model" model a64-state a64-decode a64 core
    certify_books "$root/foundations" "$work/foundations" all $foundations
    : > "$work/foundations.ready"
    printf '%s\n' 'Compiler proof foundations certified.'
}

mkdir -p "$work/tmp"
TMPDIR=$PWD/$work/tmp
export TMPDIR

case ${1-} in
    --foundations)
        [ "$#" -eq 1 ] || usage
        certify_foundations
        ;;
    --books)
        [ "$#" -ge 3 ] || usage
        package=$2
        name_p "$package" || usage
        case $package in compiler|foundations|model|tmp) usage ;; esac
        shift 2
        if [ ! -f "$work/foundations.ready" ]; then
            printf '%s\n' 'Run sh compiler/single/proofs/certify.sh --foundations first.' >&2
            exit 1
        fi
        certify_books "$root/$package" "$work/$package" all "$@"
        ;;
    '')
        [ "$#" -eq 0 ] || usage
        certify_foundations
        failed=0
        for directory in "$root"/*/; do
            [ "$directory" = "$root/foundations/" ] && continue
            [ -d "$directory" ] || continue
            if [ ! -f "${directory}certify.sh" ]; then
                printf 'Missing %scertify.sh.\n' "$directory" >&2
                failed=1
            elif ! sh "${directory}certify.sh"; then
                failed=1
            fi
        done
        exit "$failed"
        ;;
    *) usage ;;
esac
