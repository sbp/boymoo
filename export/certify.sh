#!/bin/sh
# Certifies the books of the exporter, from the root of the repository:
#
#     sh export/certify.sh
#
# It copies checks/canon.lisp, the printer of the formats, and
# export/core.lisp, the core of the exporter, into build/export/acl2/, and
# has ACL2 certify each that changed or has no certificate.  It does
# nothing that is already done.  export/book.sh runs it first.  It prints
# nothing unless something fails, and then it exits with status 1, or with
# status 3 under any version of ACL2 but the one that checks/version.lsp
# names.

dir=build/export/acl2
mkdir -p "$dir"
for b in canon core; do
    case $b in
        canon) f=checks/canon.lisp ;;
        core) f=export/core.lisp ;;
    esac
    if ! cmp -s "$f" "$dir/$b.lisp"; then
        cp "$f" "$dir/$b.lisp"
        rm -f "${dir:?}/${b:?}.cert"
    fi
    if [ ! -f "$dir/$b.cert" ]; then
        printf '(ld "checks/version.lsp")\n(certify-book "%s/%s")\n' "$dir" "$b" |
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
    fi
done
exit 0
