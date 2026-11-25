# A shell function for compiler/check.sh and compiler/test-checker.sh,
# which read this file with the command ".".

# Writes the file $1 as one field of the compiled checker's input
# (compiler/checker-entry.lisp): its length in bytes, as four bytes, the
# most significant first, and then its bytes. A file of 2^32 bytes or more
# cannot be written so; awk then ends with status 1 and writes no length.
frame_field() {
    if [ ! -s "$1" ]; then
        printf '\000\000\000\000'
        return
    fi
    bytes=$(wc -c < "$1")
    awk -v bytes="$bytes" 'BEGIN {
        if (bytes > 4294967295) exit 1
        for (place = 16777216; place >= 1; place /= 256)
            printf "%c", int(bytes / place) % 256
    }'
    cat "$1"
}
