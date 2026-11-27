set -eu
export LC_ALL=C

# The compiler is the compiled compiler named as the argument, or the
# many-pass compiler, build/compiler/compiler-2, if none is named.
if [ "$#" -gt 1 ]; then
    printf '%s\n' 'Usage: sh compiler/test-targets.sh [COMPILER]' >&2
    exit 2
fi
compiler=${1:-build/compiler/compiler-2}
case $compiler in */*) ;; *) compiler=./$compiler ;; esac
if [ ! -x "$compiler" ]; then
    if [ "$#" -eq 0 ]; then
        printf '%s\n' 'Run sh compiler/bootstrap.sh to build the compiled compiler.' >&2
    else
        printf 'There is no executable %s.\n' "$compiler" >&2
    fi
    exit 2
fi
dir=$(mktemp -d build/compiler/targets.XXXXXX)
export TMPDIR="$PWD/$dir"
image=

cleanup() {
    status=$?
    if [ -n "$image" ] && ! timeout 10 docker image rm "$image" > /dev/null; then
        status=1
    fi
    rm -rf "$dir"
    exit "$status"
}
trap cleanup 0
trap 'exit 1' HUP INT TERM

check_header() {
    od -A n -v -t u1 "$2" | awk -v target="$1" '
    function le(offset, width,    value, i) {
        for (i = offset + width - 1; i >= offset; i--)
            value = 256 * value + byte[i]
        return value
    }
    function fail(message) {
        print target ": " message
        exit 1
    }
    function macho(    count, kind, i, offset, limit, cmdsize, entry) {
        if (sprintf("%08x", le(0, 4)) != "feedfacf" ||
            le(4, 4) != 16777228 || le(12, 4) != 2)
            fail("Invalid arm64 Mach-O header.")
        # LC_SEGMENT_64 (three), LC_DYLD_INFO_ONLY, LC_LOAD_DYLINKER,
        # LC_MAIN, LC_CODE_SIGNATURE.
        count = split("00000019 00000019 00000019 80000022 0000000e 80000028 0000001d", kind)
        limit = 32 + le(20, 4)
        if (le(16, 4) != count || limit > 4096)
            fail("Invalid Mach-O load command table.")
        offset = 32
        for (i = 1; i <= count; i++) {
            cmdsize = le(offset + 4, 4)
            if (offset + 8 > limit || cmdsize < 8 || cmdsize % 8 ||
                offset + cmdsize > limit || sprintf("%08x", le(offset, 4)) != kind[i])
                fail("Invalid Mach-O load command " i ".")
            if (kind[i] == "80000028") {
                entry = le(offset + 8, 8)
                if (cmdsize != 24 || entry < 4096 || entry >= size || entry % 4)
                    fail("Invalid Mach-O entry offset.")
            }
            offset += cmdsize
        }
        if (offset != limit)
            fail("Invalid Mach-O load command size.")
        printf "Verified the arm64 Mach-O header and %d load commands (%d bytes, entry 0x%x).\n", count, size, entry
    }
    function elf(    i) {
        if (sprintf("%08x", le(0, 4)) != "464c457f" || le(4, 4) != 65794 || le(8, 8) ||
            le(16, 2) != 2 || le(18, 2) != 183 || le(20, 4) != 1 ||
            le(32, 8) != 64 || le(40, 8) || le(48, 4) ||
            le(52, 2) != 64 || le(54, 2) != 56 || le(56, 2) != 1 ||
            le(58, 2) || le(60, 2) || le(62, 2))
            fail("Invalid aarch64 ELF64 header.")
        if (le(64, 4) != 1 || le(68, 4) != 5 || le(72, 8) ||
            le(80, 8) != base || le(88, 8) != base || le(96, 8) != size ||
            le(104, 8) != size || le(112, 8) != 65536)
            fail("Invalid ELF load segment.")
        for (i = 120; i < 4096; i++)
            if (byte[i]) fail("Invalid ELF header padding.")
        if (entry_offset < 4096 || entry_offset % 4 ||
            entry_offset + 4 > size || branch != 37)
            fail("Expected an aligned ELF entry with a BL instruction.")
        printf "Verified the ELF64 header and RX load segment (%d bytes, entry 0x%x).\n", size, base + entry_offset
    }
    BEGIN { base = 4194304 }
    {
        for (i = 1; i <= NF; i++) {
            if (size < 4096) byte[size + 0] = $i + 0
            if (target == "Linux" && size == 32)
                entry_offset = le(24, 8) - base
            if (target == "Linux" && size == entry_offset + 3)
                branch = int($i / 4)
            size++
        }
    }
    END {
        if (size <= 4096) fail("The executable has no code after the header.")
        if (target == "macOS") macho()
        else elf()
    }'
}

colima_reachable() {
    command -v docker > /dev/null || return 1
    context=$(timeout 5 docker context inspect --format '{{.Name}} {{.Endpoints.docker.Host}}' 2> "$dir/docker.err") ||
        return 1
    endpoint=${context#* }
    if [ -n "${DOCKER_HOST-}" ] && [ -z "${DOCKER_CONTEXT-}" ]; then
        endpoint=$DOCKER_HOST
    fi
    case $endpoint in
        unix://*) ;;
        *) return 1 ;;
    esac
    server=$(timeout 5 docker info --format '{{.Name}}' 2> "$dir/docker.err") || return 1
    case ${context%% *}:$server in
        colima:*|colima-*:*) return 0 ;;
    esac
    case $server in
        colima|colima-*|lima-colima|lima-colima-*) return 0 ;;
        *) return 1 ;;
    esac
}

check_run() {
    target=$1
    shift
    status=0
    "$@" < "$dir/input" > "$dir/output" || status=$?
    if [ "$status" -ne 0 ]; then
        printf '%s executable exited with status %s. Expected 0.\n' "$target" "$status" >&2
        exit 1
    fi
    cmp "$dir/input" "$dir/output"
    printf '%s executable echoed its input and exited with status 0.\n' "$target"
}

{
    awk '/^\((package|hidden-package) /' spec/ground.txt
    printf '%s\n' '(define COMMON-LISP::NIL (ACL2::ECHO-INPUT (ACL2::INPUT) ACL2::INPUT))' \
        '(entry ACL2::ECHO-INPUT)'
} > "$dir/echo.program"
{ printf '(target linux)\n'; cat "$dir/echo.program"; } > "$dir/linux.program"

timeout 10 "$compiler" < "$dir/echo.program" > "$dir/macos"
timeout 10 "$compiler" < "$dir/linux.program" > "$dir/linux"
chmod +x "$dir/macos" "$dir/linux"
check_header macOS "$dir/macos"
check_header Linux "$dir/linux"

codesign -v --strict "$dir/macos"
printf '%s\n' 'codesign verified the embedded Mach-O signature.'
printf 'ACL2 Core\000\377\n' > "$dir/input"
check_run macOS timeout 5 "$dir/macos"

if ! colima_reachable; then
    printf '%s\n' 'Linux execution skipped because Docker could not reach Colima through its current context.'
    exit 0
fi
tar -cf "$dir/linux.tar" -C "$dir" linux
image=$(timeout 15 docker import --platform linux/arm64 "$dir/linux.tar")
check_run Linux timeout 15 docker run --rm -i --platform linux/arm64 --pull=never \
    --network none --read-only "$image" ./linux
