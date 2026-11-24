# Write the bytes of the proof string in the runner's canonical value.
function fail(message) {
    print message > diagnostic
    exit 1
}

{ value = $0 }

END {
    if (NR != 1)
        fail("expected one value from the runner")
    fields = split(value, parts, "\"")
    if (fields == 5 && parts[1] == "(KEYWORD::FAILURE " && parts[3] == " " && parts[5] == ")")
        fail(parts[2] (parts[4] == "" ? "" : " " parts[4]))
    if (checked) {
        if (fields != 5 || parts[1] != "(" || parts[3] != " " || parts[5] != ")")
            fail("the runner did not return proof text and a verdict")
        verdict = parts[4]
        if (verdict != "accepted" &&
            verdict !~ /^provisional skipped [0-9]+ assumed [0-9]+ given-definitions [0-9]+ given-facts [0-9]+$/)
            fail(verdict)
    } else if (fields != 3 || parts[1] != "" || parts[3] != "") {
        fail("the runner did not return proof text")
    }

    proof = parts[2]
    hex = "0123456789ABCDEF"
    # One pass: the text between escapes is written whole.  An escape is a
    # backslash and two hexadecimal digits, and a backslash is itself
    # written as an escape, so every backslash begins one.
    count = split(proof, piece, "\\")
    printf "%s", piece[1]
    for (i = 2; i <= count; i++) {
        high = index(hex, substr(piece[i], 1, 1))
        low = index(hex, substr(piece[i], 2, 1))
        if (length(piece[i]) < 2 || !high || !low)
            fail("invalid escape in proof text")
        printf "%c%s", (high - 1) * 16 + low - 1, substr(piece[i], 3)
    }
}
