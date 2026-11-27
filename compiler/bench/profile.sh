# Profiles an executable that the many-pass compiler writes, with
# sample(1) of macOS. From the root of the repository:
#
#     sh compiler/bench/profile.sh [-r RUNS] [-s SECONDS] DIR INPUT STDIN
#
# DIR is a directory of compiler/build.sh whose acl2/ holds the certified
# books of the many-pass compiler up to compile and whose compiler-2 is
# the compiler that compiler/bootstrap.sh builds from them, as
# build/compiler is after sh compiler/bootstrap.sh. INPUT is the program
# text to compile, and STDIN the standard input of the executable. ACL2
# lays out the items of INPUT as the compiler does and writes the offset
# of each named label (profile-labels.lsp); compiler-2 compiles INPUT;
# the executable runs RUNS times (3 by default) under sample, which
# records the program counter each millisecond for at most SECONDS (60 by
# default). The executable is started before its input arrives, so that
# sample can attach first; profile.py then gives each sample to the label
# at or before its program counter, leaves out the samples in sys:read,
# where the executable waits for that input, and prints the shares of
# compiled code, of each routine of the runtime and of the collector. The
# files are in DIR/profile/.
set -eu
runs=3
seconds=60
while [ $# -gt 0 ]; do
    case $1 in
        -r) runs=$2; shift 2 ;;
        -s) seconds=$2; shift 2 ;;
        *) break ;;
    esac
done
if [ $# -ne 3 ]; then
    echo 'Usage: sh compiler/bench/profile.sh [-r RUNS] [-s SECONDS] DIR INPUT STDIN' >&2
    exit 2
fi
dir=$1
input=$2
stdin=$3
work=$dir/profile
mkdir -p "$work"
absolute=$(cd "$(dirname "$input")" && pwd)/$(basename "$input")
sed "s|PROFILE-INPUT|$absolute|" compiler/bench/profile-labels.lsp > "$dir/acl2/profile-labels.lsp"
(cd "$dir/acl2" && acl2 < profile-labels.lsp > profile-labels.out 2>&1)
sed -n '/LABELS-BEGIN/,/^LABELS-END/p' "$dir/acl2/profile-labels.out" |
    grep -v 'LABELS-' > "$work/labels"
if [ ! -s "$work/labels" ]; then
    echo "compiler/bench/profile.sh: no labels; see $dir/acl2/profile-labels.out" >&2
    exit 1
fi
"$dir/compiler-2" < "$input" > "$work/profexe"
chmod +x "$work/profexe"
i=1
files=
while [ "$i" -le "$runs" ]; do
    sample profexe "$seconds" 1 -wait -mayDie -file "$work/sample-$i.txt" \
        > "$work/sample-$i.log" 2>&1 &
    pid=$!
    { sleep 2; cat "$stdin"; } | "$work/profexe" > "$work/out" 2> "$work/err" || true
    wait "$pid" || true
    files="$files $work/sample-$i.txt"
    i=$((i + 1))
done
# shellcheck disable=SC2086
python3 compiler/bench/profile.py --skip sys:read "$work/labels" profexe $files
