# Print the definitions and attachments reached by calls from entry.
# The input is in the order in which the runner loads program text.

function tokenize(line,    text, part) {
    if (!index(line, "|")) {
        gsub(/"[^"]*"/, "S", line)
        gsub(/#C\([^)]*\)/, "S", line)
    } else {
        text = ""
        while (match(line, /"[^"]*"|\|[^|]*\||#C\([^)]*\)/)) {
            text = text substr(line, 1, RSTART - 1)
            part = substr(line, RSTART, RLENGTH)
            line = substr(line, RSTART + RLENGTH)
            if (substr(part, 1, 1) == "|") {
                gsub(/ /, "\001", part)
                gsub(/\(/, "\002", part)
                gsub(/\)/, "\003", part)
                text = text part
            } else {
                text = text "S"
            }
        }
        line = text line
    }
    gsub(/\(/, " ( ", line)
    gsub(/\)/, " ) ", line)
    token_count = split(line, token, " ")
}

function skip_datum(    depth) {
    if (token[position] != "(") {
        position++
        return
    }
    depth = 0
    do {
        if (token[position] == "(") depth++
        if (token[position] == ")") depth--
        position++
    } while (depth)
}

function read_term(    head) {
    if (token[position] != "(") {
        position++
        return
    }
    position++
    if (token[position] == "(") {
        position += 2
        skip_datum()
        read_term()
        position++
    } else {
        head = token[position++]
        if (head == "COMMON-LISP::QUOTE") {
            skip_datum()
            position++
            return
        }
        if (!(head in called)) {
            called[head] = 1
            calls = calls " " head
        }
    }
    while (position <= token_count && token[position] != ")") read_term()
    position++
}

/^\(define / {
    tokenize($0)
    position = 3
    calls = ""
    skip_datum()
    while (token[position] == "(") {
        position++
        definition[token[position++]] = NR
        skip_datum()
        read_term()
        position++
    }
    for (name in called) delete called[name]
    dependencies[NR] = calls
    source[NR] = $0
}

/^\(attach / {
    tokenize($0)
    attachment[token[3]] = NR
    dependencies[NR] = token[4]
    source[NR] = $0
}

END {
    queue[1] = entry
    last = 1
    for (i = 1; i <= last; i++) {
        name = queue[i]
        line = (name in attachment) ? attachment[name] : definition[name]
        if (!line || selected[line]) continue
        selected[line] = 1
        count = split(dependencies[line], callees, " ")
        for (j = 1; j <= count; j++) queue[++last] = callees[j]
    }
    for (i = 1; i <= NR; i++)
        if (selected[i]) print source[i]
}
