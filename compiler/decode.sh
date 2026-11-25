# Writes the bytes of the string that the reference runner printed to
# the file given as the first argument.
decode_string() {
    # Bound the length of each record scanned by awk. A break can fall
    # inside a three-character byte escape, so carry that suffix forward.
    fold -b -w 4096 "$1" | awk '
        BEGIN { digits = "0123456789ABCDEF" }
        NR == 1 {
            if (substr($0, 1, 1) != "\"") exit 1
            $0 = substr($0, 2)
        }
        {
            if (closed) exit 1
            row = carry $0
            carry = ""
            end = length(row)
            for (i = 1; i <= end; i++) {
                c = substr(row, i, 1)
                if (c == "\\") {
                    if (i + 2 > end) {
                        carry = substr(row, i)
                        break
                    }
                    hi = index(digits, substr(row, i + 1, 1)) - 1
                    lo = index(digits, substr(row, i + 2, 1)) - 1
                    if (hi < 0 || lo < 0) exit 1
                    printf "%c", 16 * hi + lo
                    i += 2
                } else if (c == "\"") {
                    if (i != end) exit 1
                    closed = 1
                } else {
                    printf "%s", c
                }
            }
        }
        END { if (!closed) exit 1 }
    '
}
