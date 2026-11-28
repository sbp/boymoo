#!/bin/sh
# Certifies the proofs about the reader, the index, the data builder, the
# assembler and the writers of executables: the books of
# compiler/proofs/foundations/, then those of compiler/proofs/assembly/,
# compiler/proofs/data/ and compiler/proofs/linux/. From the root of the
# repository:
#
#     sh compiler/proofs/certify-sets.sh
#     sh compiler/proofs/certify-sets.sh --foundations
#     sh compiler/proofs/certify-sets.sh --books SET BOOK ...
#
# With no argument it certifies the foundations and then every set, by the
# certify.sh of each set's directory, which names its books in order. With
# --foundations it certifies the foundations alone, and with --books it
# certifies the books named, of the set SET, after the foundations. Each
# book is certified in build/compiler/proofs/sets/, after copying it
# there, with the packages of the compiler, of the models and of
# compiler/proofs/foundations/package.lsp.

set -eu
export LC_ALL=C

root=compiler/proofs
work=build/compiler/proofs/sets
foundations='machine kernel loading values heap interfaces'
sets='assembly data linux'

usage() {
  printf '%s\n' 'Usage: sh compiler/proofs/certify-sets.sh [--foundations | --books SET BOOK ...]' >&2
  exit 2
}

name_p() {
  case $1 in
    ''|*[!a-z0-9_-]*)
      return 1
      ;;
    *)
      return 0
      ;;
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
    model)
      packages=model
      ;;
    compiler)
      packages=compiler
      ;;
    all)
      packages='model compiler proofs'
      ;;
  esac
  portcullis=0
  for book_package in $packages
  do
    case $book_package in
      model)
        package_file=compiler/model/package.lsp
        ;;
      compiler)
        package_file=compiler/package.lsp
        ;;
      proofs)
        package_file=$root/foundations/package.lsp
        ;;
    esac
    cp "$package_file" "$stage_dir/$book_package-package.lsp"
    portcullis=$((portcullis + 1))
  done
  for book
  do
    name_p "$book" || usage
    cp "$source_dir/$book.lisp" "$stage_dir/$book.lisp"
    rm -f "$stage_dir/$book.cert"
    if ! (
      cd "$stage_dir" || exit 1
      {
        printf '%s\n' '(ld "version.lsp")'
        for book_package in $packages
        do
          printf '(ld "%s-package.lsp")\n' "$book_package"
        done
        printf '(certify-book "%s" %s nil :skip-proofs-okp nil :defaxioms-okp nil :ttags nil :pcert nil)\n' "$book" "$portcullis"
        printf '%s\n' '(good-bye)'
      } | acl2 > "$book.out" 2>&1
    ) || [ ! -s "$stage_dir/$book.cert" ]
    then
      printf 'ACL2 did not certify %s/%s.lisp. See %s/%s.out.\n' \
        "$source_dir" "$book" "$stage_dir" "$book" >&2
      return 1
    fi
    printf 'Certified %s/%s.lisp.\n' "$source_dir" "$book"
  done
}

certify_foundations() {
  rm -f "$work/foundations.ready"
  certify_books compiler "$work/compiler" compiler a64 read index data sha256 macos linux
  certify_books compiler/model "$work/model" model a64-state a64-decode a64 core
  # shellcheck disable=SC2086
  certify_books "$root/foundations" "$work/foundations" all $foundations
  : > "$work/foundations.ready"
  printf '%s\n' 'Proof foundations certified.'
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
    set_name=$2
    case " $sets " in
      *" $set_name "*)
        ;;
      *)
        usage
        ;;
    esac
    shift 2
    if [ ! -f "$work/foundations.ready" ]
    then
      printf '%s\n' 'Run sh compiler/proofs/certify-sets.sh --foundations first.' >&2
      exit 1
    fi
    certify_books "$root/$set_name" "$work/$set_name" all "$@"
    ;;
  '')
    certify_foundations
    failed=0
    for set_name in $sets
    do
      if ! sh "$root/$set_name/certify.sh"
      then
        failed=1
      fi
    done
    exit "$failed"
    ;;
  *)
    usage
    ;;
esac
