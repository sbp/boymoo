#!/bin/sh
# Certifies the books of the exporter, from the root of the repository:
#
#     sh export/certify.sh
#     sh export/certify.sh --guards
#     sh export/certify.sh --fresh-guards
#
# It copies checks/canon.lisp, the printer of the formats, and
# export/core.lisp, the core of the exporter, into build/export/acl2/, and
# has ACL2 certify each that changed or has no certificate. With
# --guards it also certifies the guard books in dependency order, and
# with --fresh-guards it certifies those books from scratch.
# export/book.sh runs it with --guards. It prints nothing unless
# something fails, and then it exits with status 1, or with status 3
# under any version of ACL2 but the one that checks/version.lsp names.

dir=build/export/acl2
mkdir -p "$dir" || exit 1
guard_books='guards-events guards-data guards-terms guards-items guards-report guards-lines guards'
books='canon core'
case ${1-} in
    --guards|--fresh-guards) books="$books $guard_books" ;;
esac
if [ "${1-}" = --fresh-guards ]; then
    for b in $guard_books; do
        rm -f "$dir/$b.cert" || exit 1
    done
fi
recertify_guards=0
for b in $books; do
    case $b in
        canon) f=checks/canon.lisp ;;
        core) f=export/core.lisp ;;
        *) f=export/proofs/$b.lisp ;;
    esac
    if ! cmp -s "$f" "$dir/$b.lisp"; then
        cp "$f" "$dir/$b.lisp" || exit 1
        rm -f "${dir:?}/${b:?}.cert" || exit 1
    fi
    case $b in
        guards*)
            if [ "$recertify_guards" -eq 1 ]; then
                rm -f "${dir:?}/${b:?}.cert" || exit 1
            fi ;;
    esac
    if [ ! -f "$dir/$b.cert" ]; then
        if [ "$b" = core ]; then
            for dependent in $guard_books; do
                rm -f "$dir/$dependent.cert" || exit 1
            done
        fi
        printf '(ld "checks/version.lsp")\n(certify-book "%s/%s" 0 :default :skip-proofs-okp nil :defaxioms-okp nil :ttags nil :pcert nil)\n' "$dir" "$b" |
            timeout 1800 acl2 > "$dir/$b.out" 2>&1
        status=$?
        if [ $status -eq 3 ]; then
            echo "export/certify.sh stopped: $(sed -n 's/^version: //p' "$dir/$b.out")" >&2
            exit 3
        fi
        if [ ! -f "$dir/$b.cert" ]; then
            echo "export/certify.sh: ACL2 did not certify $f; see $dir/$b.out" >&2
            exit 1
        fi
        if [ "$b" != canon ]; then
            recertify_guards=1
        fi
    fi
done
exit 0
