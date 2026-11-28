set -eu
export LC_ALL=C

usage() {
    printf '%s\n' 'Usage: sh compiler/bench/run.sh [--quick] [REFERENCE [CANDIDATE]]' >&2
    exit 2
}

fail() {
    printf 'compiler/bench/run.sh: %s\n' "$*" >&2
    exit 1
}

quick=0
while [ "$#" -gt 0 ]; do
    case $1 in
        --quick) quick=1; shift ;;
        --) shift; break ;;
        -*) usage ;;
        *) break ;;
    esac
done
[ "$#" -le 2 ] || usage

reference=${1-build/compiler/compiler-2}
candidate=${2-}
[ -f "$reference" ] && [ -x "$reference" ] || fail "no executable compiler $reference"
case $reference in */*) ;; *) reference=./$reference ;; esac
if [ -n "$candidate" ]; then
    [ -f "$candidate" ] && [ -x "$candidate" ] || fail "no executable compiler $candidate"
    case $candidate in */*) ;; *) candidate=./$candidate ;; esac
fi

compiler_input=build/compiler/compiler.input
checker_input=build/compiler/checker-test/checker.input
[ -s "$compiler_input" ] || fail 'run sh compiler/bootstrap.sh first'
if [ "$quick" -eq 0 ]; then
    [ -s "$checker_input" ] || fail 'run sh compiler/build-checker.sh first'
    [ -s build/export/library.statements ] || fail 'missing build/export/library.statements'
    [ -s build/prover/library.proofs ] || fail 'missing build/prover/library.proofs'
fi

mkdir -p build/compiler/bench
dir=$(mktemp -d build/compiler/bench/run.XXXXXX)
printf 'Benchmark results are in %s.\n' "$dir" >&2
printf 'benchmark input\n' > "$dir/small.input"
: > "$dir/empty"

read_system_time() {
    awk '$2 == "real" { elapsed = $1 }
         $2 == "maximum" && $3 == "resident" && $4 == "set" && $5 == "size" { peak = $1 }
         END {
             if (elapsed == "" || peak == "") exit 1
             print elapsed, peak
         }' "$1"
}

timer=time-l
if ! (command -p time -l true) 2> "$dir/time.probe" ||
   ! read_system_time "$dir/time.probe" > /dev/null; then
    command -v python3 > /dev/null || fail 'time -l did not report peak RSS and python3 is unavailable'
    timer=wait4
fi

printf 'reference\t%s\ncandidate\t%s\ntimer\t%s\nstarted\t%s\n' \
    "$reference" "$candidate" "$timer" "$(date '+%Y-%m-%d %H:%M:%S %z')" > "$dir/run.tsv"
printf 'benchmark\tcompiler\tsample\telapsed_seconds\tpeak_resident_bytes\texit_status\n' \
    > "$dir/samples.tsv"
printf 'benchmark\tcompiler\truns\telapsed_seconds\tpeak_resident_bytes\n' \
    > "$dir/results.tsv"

. compiler/frame.sh

frame_checker() {
    frame_field spec/ground.txt &&
    frame_field build/export/library.statements &&
    frame_field "$dir/empty" &&
    frame_field "$dir/empty" &&
    frame_field build/prover/library.proofs
}

measure() {
    if [ "$timer" = time-l ]; then
        measure_status=0
        (command -p time -l sh -c 'exec "$1" > "$2" 2> "$3"' \
            sh "$1" "$2.out" "$2.err") 2> "$2.time" || measure_status=$?
        read_system_time "$2.time" > "$2.measure" || fail "could not read timing for $2"
        return "$measure_status"
    fi
    python3 compiler/bench/measure.py "$1" "$2.out" "$2.err" > "$2.measure"
}

median() {
    sort -k "$1,$1" -n "$2" | awk -v column="$1" -v middle="$3" 'NR == middle { print $column }'
}

run_side() {
    side=$1
    side_compiler=$2
    exe=$dir/$benchmark.$side.exe
    side_samples=$dir/$benchmark.$side.samples
    : > "$side_samples"
    "$side_compiler" < "$program_input" > "$exe" 2> "$exe.err" || {
        cat "$exe.err" >&2
        fail "$side compiler could not compile $benchmark"
    }
    [ -s "$exe" ] || fail "$side compiler wrote an empty executable for $benchmark"
    chmod +x "$exe"

    sample=1
    while [ "$sample" -le "$runs" ]; do
        stem=$dir/$benchmark.$side.$sample
        status=0
        if [ "$benchmark" = checker ]; then
            (frame_checker && : > "$stem.frame-complete") | measure "$exe" "$stem" || status=$?
        else
            measure "$exe" "$stem" < "$stdin_file" || status=$?
        fi
        read -r elapsed peak < "$stem.measure" || fail "missing timing for $stem"
        printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
            "$benchmark" "$side" "$sample" "$elapsed" "$peak" "$status" >> "$dir/samples.tsv"
        [ "$status" -eq 0 ] || {
            cat "$stem.err" >&2
            fail "$side executable for $benchmark exited with status $status"
        }
        if [ "$benchmark" = checker ]; then
            [ -f "$stem.frame-complete" ] || fail 'could not write the complete checker input'
        fi
        if [ -n "$expected_file" ]; then
            cmp "$expected_file" "$stem.out" || fail "unexpected output from $side $benchmark"
        else
            [ -s "$stem.out" ] || fail "$side executable for $benchmark wrote no output"
        fi
        if [ "$sample" -gt 1 ]; then
            cmp "$dir/$benchmark.$side.1.out" "$stem.out" || fail "inconsistent $side output for $benchmark"
            cmp "$dir/$benchmark.$side.1.err" "$stem.err" || fail "inconsistent $side errors for $benchmark"
            rm -f "$stem.out"
        fi
        printf '%s\t%s\n' "$elapsed" "$peak" >> "$side_samples"
        sample=$((sample + 1))
    done

    middle=$(((runs + 1) / 2))
    elapsed=$(median 1 "$side_samples" "$middle")
    peak=$(median 2 "$side_samples" "$middle")
    printf '%s\t%s\t%s\t%s\t%s\n' "$benchmark" "$side" "$runs" "$elapsed" "$peak" \
        >> "$dir/results.tsv"
}

run_benchmark() {
    benchmark=$1
    program_input=$2
    stdin_file=$3
    expected_file=$4
    runs=$5
    run_side reference "$reference"
    if [ -n "$candidate" ]; then
        run_side candidate "$candidate"
        cmp "$dir/$benchmark.reference.1.out" "$dir/$benchmark.candidate.1.out" ||
            fail "compiler outputs disagree for $benchmark"
        cmp "$dir/$benchmark.reference.1.err" "$dir/$benchmark.candidate.1.err" ||
            fail "compiler error outputs disagree for $benchmark"
    fi
    rm -f "$dir/$benchmark.reference.exe" "$dir/$benchmark.candidate.exe"
    if [ "$benchmark" = compiler ]; then
        rm -f "$dir/$benchmark.reference.1.out" "$dir/$benchmark.candidate.1.out"
    fi
}

run_benchmark compiler "$compiler_input" "$compiler_input" '' 3
if [ "$quick" -eq 0 ]; then
    printf 'accepted\n' > "$dir/checker.expected"
    run_benchmark checker "$checker_input" '' "$dir/checker.expected" 1
fi
for name in calls arithmetic conses strings; do
    printf '%s ok' "$name" > "$dir/$name.expected"
    run_benchmark "$name" "compiler/bench/$name.program" "$dir/small.input" "$dir/$name.expected" 3
done
cat "$dir/results.tsv"
