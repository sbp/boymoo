# Compiled program benchmarks

Run the benchmarks from the repository root on macOS after building the compiler and the checker's input with `sh compiler/bootstrap.sh` and `sh compiler/build-checker.sh`. The library check uses `build/export/library.statements` and `build/prover/library.proofs`.

```sh
sh compiler/bench/run.sh [--quick] [REFERENCE [CANDIDATE]]
```

`REFERENCE` is the compiled compiler whose executables are measured, by default `build/compiler/compiler-2`. With `CANDIDATE`, a second compiled compiler, each benchmark is also compiled and run with it, and the two compilers' executables must give the same output and error output, byte for byte. `--quick` skips the library check. To check the benchmark harness, give the same compiler twice.

The compiler benchmark compiles the compiler's own input, `build/compiler/compiler.input`, and runs the resulting executable on that input. The checker benchmark gives the compiled checker the library check described in `compiler/README.md`, with the input framed by `compiler/frame.sh` and streamed through a pipe. The smaller benchmarks exercise a recursive call of eleven arguments, arithmetic on large fractions, allocation of temporary conses while keeping a list live under a 4 MiB heap limit, and a string slice with zero padding. Each successful run checks the exit status and the benchmark outputs. The checker must return `accepted` followed by a line feed. The smaller programs return a string after checking their results against a value in the program text.

Each invocation writes a new `build/compiler/bench/run.XXXXXX/` directory. `results.tsv` gives elapsed seconds and peak resident bytes, taking the median of three samples for each short benchmark and one sample for the checker. `samples.tsv` keeps each measurement and `run.tsv` records the compiler paths, timer and start time. After successful output comparisons the script removes the generated executables and the binary compiler output. It keeps the timing records and the first checker and small-program outputs. The script uses the system `time -l`, or Python's `wait4` and a monotonic clock when the system timer cannot report resource usage.

## Prover workloads

```sh
sh compiler/bench/prover.sh PROVER-INPUT [EXPORT [BOOK ...]]
```

`sh compiler/build-prover.sh` produces `build/compiler/prover-build/prover.input` after the prover build described in `prover/README.md`. `EXPORT` defaults to `build/export`. It must contain the library statements and the statements and aids for each requested book, as produced by `sh export/run.sh BOOK ...`. The default books are `build/choice` and `misc/hidden-defpkg-checks/top`. The compiled compiler is `build/compiler/compiler-2`, or the one that `COMPILER` names.

The `compile-prover` workload has the compiler compile the prover input. For each book, the prover so made reads the library, the book's statements and its aids, framed as `prover/README.md` describes, and must exit successfully and write a proof file. The script uses Python's `wait4` and a monotonic clock, writes timings to `build/compiler/bench/prover.XXXXXX/results.tsv`, and removes the proof files and the prover when it is done.

## Measurements

Benchmarks on macOS on 2026-11-27 gave the results below for the executables that `build/compiler/compiler-2` writes. Its runtime sets the next old-space collection target to three halves of the bytes that survive a full copy when at least 128 MiB survive.

```sh
sh compiler/bench/run.sh
sh compiler/bench/prover.sh build/compiler/prover-build/prover.input build/export \
    misc/dft-ex build/choice misc/hidden-defpkg-checks/top \
    arithmetic/equalities std/basic/arith-equivs
```

| Workload | Seconds | Peak bytes |
| --- | ---: | ---: |
| Checker library check | 13.06 | 331,808,768 |
| Calls | 0.00 | 1,081,344 |
| Arithmetic | 0.04 | 2,146,304 |
| Conses | 0.02 | 3,801,088 |
| Strings | 0.00 | 1,114,112 |
| Prover on `misc/dft-ex` | 137.074442 | 1,129,086,976 |
| Prover on `build/choice` | 13.015923 | 641,007,616 |
| Prover on `misc/hidden-defpkg-checks/top` | 14.857133 | 581,615,616 |
| Prover on `arithmetic/equalities` | 43.919263 | 628,129,792 |
| Prover on `std/basic/arith-equivs` | 206.004227 | 794,116,096 |

On 2026-11-28, `sh compiler/bench/run.sh --quick` gave 1.97 seconds and 58,851,328 peak bytes for the compiled compiler compiling its own input.

## Profiles

```sh
sh compiler/bench/profile.sh [-r RUNS] [-s SECONDS] DIR INPUT STDIN
```

profiles the executable that the many-pass compiler writes from `INPUT`, run on `STDIN`, with `sample`, the sampling profiler of macOS. `DIR` is a build directory of `compiler/build.sh` with the certified books up to `compile` in `DIR/acl2/` and the compiler built from them as `DIR/compiler-2`, as `build/compiler` is after `sh compiler/bootstrap.sh`. The executables have no symbols, so ACL2 lays out the items of `INPUT` as the compiler does and writes the offset of every named label (`profile-labels.lsp`); `profile.py` then gives each sample to the label at or before its program counter. It prints the shares of the compiled functions together, of each routine of the runtime, of the collector and of the system calls, and the forty labels with the most samples. Samples in `sys:read` are left out, as the executable waits there for its input while `sample` attaches.

Run on 2026-11-27 with `sh compiler/bench/profile.sh -r 1 -s 120 DIR build/compiler/checker-test/checker.input FRAMED`, where `FRAMED` is the library check of `compiler/README.md` framed by `compiler/frame.sh`, the compiled checker gave 19,221 samples: 49% in compiled code, 33% in the collector (`rt:forward-pointer` alone 17%), 2% in `sys:release`, and 11% outside the executable, in the system. The functions with the most samples were `BOYMOO::APP`, `STRING-CHARS`, `TRIE-CHILD`, `STRING-LINES` and `SUM`, each with 4% to 6%.
