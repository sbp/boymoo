# The checker's library: the define lines of ACL2's library that the
# checker needs.  checker/build.sh runs it, from the root of the
# repository, as
#
#     awk -f checker/library.awk spec/ground.txt CHECKER LIBRARY
#
# where CHECKER is the checker's exported statements and LIBRARY is
# build/export/library.statements.  It prints, in the order of LIBRARY,
# each define line of LIBRARY that defines a function that the checker
# calls, or that a line so printed calls, and that neither the ground
# theory nor the checker defines.  A call is the function at the head of
# a term in the body of a definition, at any depth outside a quoted
# constant; the formals of a lambda are not terms.  The lines are ACL2's
# own, as the exporter wrote them, and are both statements and program
# text (spec/formats.md, section 5).

# The tokens of the line: parentheses and the texts of atoms
# (spec/formats.md, section 2), split at spaces.  A string, which has no "
# inside, becomes S and a complex rational, #C( ... ), becomes C: neither
# names a function.  In a part of a symbol between bars, which has no |
# inside, a space or a parenthesis becomes a byte that no line holds.
function tokens(s,    part) {
    gsub(/"[^"]*"/, "S", s)
    gsub(/#C\([^)]*\)/, "C", s)
    while (match(s, /\|[^|]*\|/)) {
        part = substr(s, RSTART + 1, RLENGTH - 2)
        gsub(/ /, "\001", part)
        gsub(/\(/, "\002", part)
        gsub(/\)/, "\003", part)
        s = substr(s, 1, RSTART - 1) "\004" part "\004" substr(s, RSTART + RLENGTH)
    }
    gsub(/\(/, " ( ", s)
    gsub(/\)/, " ) ", s)
    return split(s, tok, " ")
}

function skip_datum(    d) {
    if (tok[ti] != "(") {
        ti++
        return
    }
    d = 0
    do {
        if (tok[ti] == "(")
            d++
        else if (tok[ti] == ")")
            d--
        ti++
    } while (d > 0)
}

# Reads the term at tok[ti] and adds to the string calls each function
# that it calls.
function term(    h) {
    if (tok[ti] != "(") {
        ti++
        return
    }
    ti++
    if (tok[ti] == "(") {            # ((lambda formals body) actuals ...)
        ti += 2
        skip_datum()
        term()
        ti++
    } else {
        h = tok[ti++]
        if (h == "COMMON-LISP::QUOTE") {
            skip_datum()
            ti++
            return
        }
        calls = calls " " h
    }
    while (tok[ti] != ")")
        term()
    ti++
}

# Reads the define line in tok: the names it defines go into the string
# names, and the functions its bodies call into calls.
function define_line() {
    names = ""
    calls = ""
    ti = 3
    skip_datum()                     # the ruler-extenders
    while (tok[ti] == "(") {
        ti++
        names = names " " tok[ti++]
        skip_datum()                 # the formals
        term()
        ti++
    }
}

FNR == 1 { file++ }

/^\(primitive / && file == 1 { split($0, f, "[ ()]+"); known[f[3]] = 1; next }

!/^\(define / { next }

{
    tokens($0)
    define_line()
    k = split(names, f, " ")
}

file == 1 || file == 2 { for (i = 1; i <= k; i++) known[f[i]] = 1 }

file == 2 { need = need calls }

file == 3 {
    for (i = 1; i <= k; i++)
        if (!(f[i] in line_of))
            line_of[f[i]] = FNR
    text[FNR] = $0
    callees[FNR] = calls
}

END {
    n = split(need, todo, " ")
    for (i = 1; i <= n; i++) {
        g = todo[i]
        if (g in known || !(g in line_of) || (line_of[g] in chosen))
            continue
        chosen[line_of[g]] = 1
        m = split(callees[line_of[g]], more, " ")
        for (j = 1; j <= m; j++)
            todo[++n] = more[j]
    }
    for (l = 1; l <= FNR; l++)
        if (l in chosen)
            print text[l]
}
