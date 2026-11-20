# Turn the hexadecimal bytes from od into an ECMAScript string.
BEGIN {
    for (i = 32; i <= 126; i++) {
        if (i != 34 && i != 92) {
            printable[sprintf("%02x", i)] = sprintf("%c", i)
        }
    }
    print "boymooInputs.push(["
}
{
    for (i = 1; i <= NF; i++) {
        byte = $i
        chunk = chunk ((byte in printable) ? printable[byte] : "\\x" byte)
        if (++lengthInBytes == 2048) {
            printf "\"%s\",\n", chunk
            chunk = ""
            lengthInBytes = 0
        }
    }
}
END {
    printf "\"%s\"].join(\"\"));\n", chunk
}
