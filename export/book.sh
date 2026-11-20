#!/bin/sh
# Exports one book, or ACL2's built-in library, and reads the files back.
# export/run.sh calls it, from the root of the repository, as
#
#     sh export/book.sh NAME
#
# where NAME is :library, or the name of a book: one of ACL2's
# distributed books, given relative to ACL2's directory of books (for
# example std/lists/append), or a book of this repository certified into
# build/ (a name that begins with build/).  It writes, for a book, the
# files build/export/books/NAME.statements, .program, .aids, .notes,
# .readback and .log, and for the library build/export/library.* in the
# same way.  It needs build/export/ground-fns.lsp, which export/run.sh
# writes.

name=$1
case $name in
    :library) out=build/export/library ;;
    *) out=build/export/books/$name ;;
esac
mkdir -p "$(dirname "$out")"
rm -f "$out.statements" "$out.program" "$out.aids" "$out.notes" \
      "$out.readback" "$out.log"

# A book is included only if it has a valid certificate, so that what is
# exported is what ACL2 has certified.  A book that uses a trust tag is
# allowed, and its notes say so.
case $name in
    :library) include='' ;;
    build/*) include="(include-book \"$name\" :uncertified-okp nil :ttags :all)" ;;
    *) include="(include-book \"$name\" :dir :system :uncertified-okp nil :ttags :all)" ;;
esac

{
    echo '(in-package "ACL2")'
    echo "(set-inhibit-output-lst '(warning warning! observation prove proof-tree event summary history))"
    echo '(assign bx-boot-hi (max-absolute-event-number (w state)))'
    echo "$include"
    echo '(assign bx-hi (max-absolute-event-number (w state)))'
    echo '(ld "build/export/ground-fns.lsp")'
    echo '(ld "checks/canon.lsp")'
    echo '(ld "export/export.lsp")'
    echo '(set-inhibit-output-lst nil)'
    case $name in
        :library)
            echo "(bx-export-library (@ bx-ground-fns) (@ bx-hi) \"$out\" state)"
            echo '(ld "export/readback.lsp")'
            echo "(rb-readback \"$out\" :library 0 (@ bx-hi) (@ bx-ground-fns) state)" ;;
        *)
            # Including the book adds at least its own event; if the world
            # did not grow, the book was not included and nothing is written.
            echo "(if (< (@ bx-boot-hi) (@ bx-hi))
                      (bx-export-book (@ bx-ground-fns) (@ bx-boot-hi) (@ bx-boot-hi)
                                      (@ bx-hi) \"$out\" state)
                    (value :not-included))"
            echo '(ld "export/readback.lsp")'
            echo "(if (< (@ bx-boot-hi) (@ bx-hi))
                      (rb-readback \"$out\" :book (@ bx-boot-hi) (@ bx-hi) (@ bx-ground-fns) state)
                    (value :not-included))" ;;
    esac
    echo '(good-bye)'
} | timeout 1800 acl2 > "$out.log" 2>&1
status=$?
if [ $status -ne 0 ]; then echo "(exit $status)" >> "$out.log"; fi
exit 0
