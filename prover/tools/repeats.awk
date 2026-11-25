# Leave out of a proof file each define, lemma or choose entry whose head
# line was written before, with its proofs and, for a definition, the
# measure or skip entry that follows it for it.  A helper entry is named by
# its content, so the same head line is the same helper: one stated by an
# earlier piece of the library's proofs, or, with -v known=FILE, by the
# head lines of FILE (the library's proofs, which a checker reads first).
#
#     awk [-v known=FILE] -f prover/tools/repeats.awk [PROOFS]
BEGIN {
    if (known != "")
        while ((getline line < known) > 0)
            if (line ~ /^\((define|lemma|choose) /) seen[line] = 1
}
function head_word(line) {
    if (line ~ /^\(define /) return "define"
    if (line ~ /^\(lemma /) return "lemma"
    if (line ~ /^\(choose /) return "choose"
    if (line ~ /^\(theorem /) return "theorem"
    if (line ~ /^\(measure /) return "measure"
    if (line ~ /^\(witness /) return "witness"
    if (line ~ /^\(skip /) return "skip"
    return ""
}
function first_function(line,    s, depth, i, c) {
    s = substr(line, 9)
    if (substr(s, 1, 1) == "(") {
        depth = 0
        for (i = 1; i <= length(s); i++) {
            c = substr(s, i, 1)
            if (c == "(") depth++
            else if (c == ")") { depth--; if (depth == 0) break }
        }
        s = substr(s, i + 1)
    } else
        sub(/^[^ ]+/, "", s)
    sub(/^ \(/, "", s)
    sub(/ .*$/, "", s)
    return s
}
function entry_name(line,    s) {
    s = line
    sub(/^\([a-z]+ /, "", s)
    sub(/[ )].*$/, "", s)
    return s
}
{
    w = head_word($0)
    if (w == "") { if (!dropping) print; next }
    if (w == "define" || w == "lemma" || w == "choose") {
        if ($0 in seen) { dropping = 1; waiting = (w == "define") ? first_function($0) : ""; next }
        seen[$0] = 1; dropping = 0; waiting = ""; print; next
    }
    if ((w == "measure" || w == "skip") && waiting != "" && entry_name($0) == waiting) { waiting = ""; dropping = 1; next }
    dropping = 0; waiting = ""; print
}
