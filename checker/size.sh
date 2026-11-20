#!/bin/sh
# The size of the checker's source: for each of its books, the lines that
# are neither blank nor wholly comment, a comment being what follows a
# semicolon on a line.  Run from the root of the repository:
#
#     sh checker/size.sh

for b in base read terms rules admit check; do
    awk -v f="checker/$b.lisp" '
        { line = $0; sub(/^[ \t]*/, "", line)
          if (line != "" && substr(line, 1, 1) != ";") n++ }
        END { printf "%6d %s\n", n, f }' "checker/$b.lisp"
done | awk '{ print; total += $1 } END { printf "%6d total\n", total }'
