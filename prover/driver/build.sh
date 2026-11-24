#!/bin/sh
# Certify the driver and export its ACL2 Core program from the repository root.
set -eu

source_dir=prover/driver
work=build/prover/driver
shared=build/prover/acl2
books=$work/acl2
checker=$books/checker
exported=$work/export/driver
set_books='open t2/open t3/open t4/open h1/open h2/open h3/open h4/open b1/open b2/open l1/open'

fail() {
    printf 'prover/driver/build.sh: %s\n' "$*" >&2
    exit 1
}

# Eight sets certify their books under build/prover/SET/acl2, and the driver
# reads the books of every set under build/prover/acl2/SET.
for set in t2 t3 t4 h1 h2 h4 b1 l1; do
    if [ -d "build/prover/$set/acl2" ] && [ ! -e "$shared/$set" ]; then
        ln -s "../$set/acl2" "$shared/$set" || fail "could not link $shared/$set"
    fi
done
for dependency in package.lsp reader.cert; do
    [ -s "$shared/$dependency" ] || fail "missing $shared/$dependency"
done
for dependency in $set_books; do
    if [ ! -s "$shared/$dependency.cert" ] ||
       [ ! -s "$shared/$dependency.lisp" ] ||
       [ "$shared/$dependency.lisp" -nt "$shared/$dependency.cert" ]; then
        fail "waiting for the certified $shared/$dependency"
    fi
done

mkdir -p "$work" "$checker"
mkdir "$work/build.lock" || fail 'a driver build is already in progress'
temporary="$exported.tmp.$$"
trap 'rm -f "$temporary".statements "$temporary".program "$temporary".aids "$temporary".notes "$temporary".readback
      rm -rf "$work/build.lock"' 0
trap 'exit 1' HUP INT TERM

copy_changed() {
    cmp -s "$1" "$2" || cp "$1" "$2"
}

certify() {
    book_path=$1
    portcullis=$2
    shift 2
    rm -f "$book_path.cert"
    {
        printf '%s\n' '(ld "checks/version.lsp")'
        printf '%s\n' "(set-ld-error-action '(:exit 1) state)"
        printf '%s\n' "(set-inhibit-output-lst '(proof-tree prove observation history warning warning!))"
        printf '%s\n' "$@"
        printf '(certify-book "%s" %s :default :skip-proofs-okp nil :defaxioms-okp nil :ttags nil)\n' \
            "$book_path" "$portcullis"
        printf '%s\n' '(good-bye)'
    } > "$work/certify.in"
    if ! sh prover/tools/acl2.sh < "$work/certify.in" > "$book_path.out" 2>&1 ||
       [ ! -s "$book_path.cert" ]; then
        fail "ACL2 did not certify $book_path. See $book_path.out."
    fi
}

# The checker has its own package and certification chain.
copy_changed checker/package.lsp "$checker/package.lsp"
previous=$checker/package.lsp
for book in base read terms rules admit check; do
    path=$checker/$book
    copy_changed "checker/$book.lisp" "$path.lisp"
    if [ ! -s "$path.cert" ] || [ "$path.lisp" -nt "$path.cert" ] ||
       [ "$previous" -nt "$path.cert" ]; then
        certify "$path" 1 "(ld \"$checker/package.lsp\" :ld-error-action :error)"
    fi
    previous=$path.cert
done

load_package="(ld \"$shared/package.lsp\" :ld-error-action :error)"
while IFS= read -r book; do
    path=$books/$book
    copy_changed "$source_dir/$book.lisp" "$path.lisp"
    stale=0
    if [ ! -s "$path.cert" ] || [ "$path.lisp" -nt "$path.cert" ] ||
       [ "$shared/package.lsp" -nt "$path.cert" ]; then
        stale=1
    fi
    case $book in
        worklist)
            [ ! "$shared/reader.cert" -nt "$path.cert" ] || stale=1
            if [ "$stale" -eq 1 ]; then
                certify "$path" 2 "$load_package" \
                    "(include-book \"$shared/reader\" :uncertified-okp nil)"
            fi ;;
        prove)
            [ ! "$books/worklist.cert" -nt "$path.cert" ] || stale=1
            if [ "$stale" -eq 1 ]; then
                certify "$path" 2 "$load_package" \
                    "(include-book \"$books/worklist\" :uncertified-okp nil)"
            fi ;;
        driver)
            for dependency in "$books/worklist.cert" "$books/prove.cert" "$checker/check.cert"; do
                [ ! "$dependency" -nt "$path.cert" ] || stale=1
            done
            for dependency in $set_books; do
                [ ! "$shared/$dependency.cert" -nt "$path.cert" ] || stale=1
            done
            if [ "$stale" -eq 1 ]; then
                certify "$path" 2 "$load_package" \
                    "(ld \"$checker/package.lsp\" :ld-error-action :error)"
            fi ;;
        *) fail "unknown book $book in $source_dir/ORDER" ;;
    esac
done < "$source_dir/ORDER"

readback_agrees() {
    awk '{ found = $NF; sub(/\)$/, "", found)
           if (found !~ /^[0-9]+$/ || $(NF - 1) != found) bad = 1 }
         /^\(readback / { readbacks++ }
         END { exit (bad || readbacks != 2 || NR < 6) }' "$1"
}

export_current() {
    for suffix in program statements notes readback; do
        [ -s "$exported.$suffix" ] &&
            [ ! "$books/driver.cert" -nt "$exported.$suffix" ] || return 1
    done
    readback_agrees "$exported.readback"
}

# Export and readback each use their own ACL2 heap.
if ! export_current; then
    for dependency in ground-fns.lsp acl2/canon.cert acl2/guards.cert; do
        [ -s "build/export/$dependency" ] || fail "missing build/export/$dependency"
    done
    mkdir -p "$(dirname "$exported")"
    {
        printf '%s\n' '(ld "checks/version.lsp")'
        printf '%s\n' "(set-ld-error-action '(:exit 1) state)"
        printf '%s\n' "(set-inhibit-output-lst '(warning warning! observation prove proof-tree event summary history))"
        printf '%s\n' '(assign bx-boot-hi (max-absolute-event-number (w state)))'
        printf '(include-book "%s/driver" :uncertified-okp nil)\n' "$books"
        printf '%s\n' '(assign bx-hi (max-absolute-event-number (w state)))'
        printf '%s\n' '(ld "build/export/ground-fns.lsp")'
        printf '%s\n' '(include-book "build/export/acl2/canon" :uncertified-okp nil)'
        printf '%s\n' '(include-book "build/export/acl2/guards" :uncertified-okp nil)'
    } > "$work/export-base.in"
    {
        cat "$work/export-base.in"
        printf '%s\n' '(ld "export/export.lsp")'
        printf '%s\n' '(set-guard-checking t)'
        printf '(bx-export-book (@ bx-ground-fns) (@ bx-boot-hi) (@ bx-boot-hi) (@ bx-hi) "%s" state)\n' "$temporary"
        printf '%s\n' '(cw "~%driver export complete~%")' '(good-bye)'
    } > "$work/export.in"
    if ! sh prover/tools/acl2.sh < "$work/export.in" > "$exported.log" 2>&1 ||
       ! grep -Fxq 'driver export complete' "$exported.log" ||
       [ ! -s "$temporary.program" ] || [ ! -s "$temporary.statements" ]; then
        fail "the driver export failed. See $exported.log."
    fi

    {
        cat "$work/export-base.in"
        printf '%s\n' '(ld "export/readback.lsp")'
        printf '%s\n' '(value-triple #+sbcl (gc$ :full t) #-sbcl (gc$))'
        printf '(rb-readback "%s" :book (@ bx-boot-hi) (@ bx-hi) (@ bx-ground-fns) state)\n' "$temporary"
        printf '%s\n' '(good-bye)'
    } > "$work/readback.in"
    if ! sh prover/tools/acl2.sh < "$work/readback.in" > "$work/readback.log" 2>&1 ||
       [ ! -s "$temporary.readback" ] || ! readback_agrees "$temporary.readback"; then
        fail "the driver export did not pass readback. See $work/readback.log."
    fi
    if [ -d "$work/fastcache" ]; then
        rm -r "$work/fastcache"
    fi
    for suffix in statements aids notes readback program; do
        mv "$temporary.$suffix" "$exported.$suffix"
    done
    export_current || fail "the driver export is incomplete. See $exported.log."
fi
printf '%s\n' 'Certified and exported driver.'
