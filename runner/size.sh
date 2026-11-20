#!/bin/sh
# The size of the runner's C source: for each file, its lines that are
# neither blank nor wholly comment.  Run from the root of the repository:
#
#     sh runner/size.sh

for f in runner/run.h runner/sys.c runner/heap.c runner/num.c runner/data.c runner/eval.c; do
    awk -v f=$f '
        { line = $0; code = ""
          while (line != "") {
              if (incomment) {
                  i = index(line, "*/")
                  if (i == 0) { line = ""; break }
                  line = substr(line, i + 2); incomment = 0
              } else {
                  i = index(line, "/*")
                  if (i == 0) { code = code line; break }
                  code = code substr(line, 1, i - 1); line = substr(line, i + 2); incomment = 1
              }
          }
          if (code ~ /[^ \t]/) n++ }
        END { printf "%6d %s\n", n, f }' $f
done | awk '{ print; total += $1 } END { printf "%6d total\n", total }'
