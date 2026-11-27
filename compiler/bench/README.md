# Compiled program benchmarks

Run the benchmarks from the repository root on macOS after building the single-pass compiler and the checker's input with `sh compiler/single/bootstrap.sh` and `sh compiler/build-checker.sh`. `sh compiler/bootstrap.sh` builds the candidate compiler, the many-pass compiler. The library check uses `build/export/library.statements` and `build/prover/library.proofs`.

```sh
sh compiler/bench/run.sh [--baseline] [--quick] [REFERENCE [CANDIDATE]]
```

The default reference is the single-pass compiler, `build/compiler/single/compiler-2`, and the default candidate is the many-pass compiler, `build/compiler/compiler-2`, when it exists. `--baseline` runs only the reference. `--quick` skips the library check. To check the benchmark harness with identical compilers, give `build/compiler/single/compiler-2` twice.

The two compilers receive the same program text for each benchmark. The compiler benchmark compiles the single-pass compiler and runs the resulting executables on its input, `build/compiler/single/compiler.input`. The checker benchmark gives the resulting checkers the library check described in `compiler/README.md`, with the input framed by `compiler/frame.sh` and streamed through a pipe. The smaller benchmarks exercise a recursive call of eleven arguments, arithmetic on large fractions, allocation of temporary conses while keeping a list live under a 4 MiB heap limit, and a string slice with zero padding. Each successful run checks the exit status and the benchmark outputs. The checkers must return `accepted` followed by a line feed. The smaller programs return a string after checking their results against a value in the program text.

Each invocation writes a new `build/compiler/bench/run.XXXXXX/` directory. `results.tsv` gives elapsed seconds and peak resident bytes, taking the median of three samples for each short benchmark and one sample for the checker. `samples.tsv` keeps each measurement and `run.tsv` records the compiler paths, timer and start time. After successful output comparisons the script removes the generated executables and the binary compiler output. It keeps the timing records and the first checker and small-program outputs. The script uses the system `time -l`, or Python's `wait4` and a monotonic clock when the system timer cannot report resource usage.

## Prover workloads

```sh
sh compiler/bench/prover.sh PROVER-INPUT [EXPORT [BOOK ...]]
```

`sh compiler/build-prover.sh` produces `build/compiler/prover-build/prover.input` after the prover build described in `prover/README.md`. `EXPORT` defaults to `build/export`. It must contain the library statements and the statements and aids for each requested book, as produced by `sh export/run.sh BOOK ...`. The default books are `build/choice` and `misc/hidden-defpkg-checks/top`.

The `compile-prover` workload runs two executables of the single-pass compiler, whose program text is `build/compiler/single/compiler.input`, on the prover input. The reference is `build/compiler/single/compiler-2`. The candidate is built from the same compiler input by `build/compiler/compiler-2`. The benchmark compares the prover files they write byte for byte.

For each prover workload, both compilers build the prover from the same program text. The benchmark streams the library, book statements and aids using the framing in `prover/README.md`. It compares the two proof files and the standard error bytes and requires each run to exit successfully. It uses Python's `wait4` and a monotonic clock, writes timings to `build/compiler/bench/prover.XXXXXX/results.tsv`, and removes the temporary proof files and executables after comparison.

## Measurements

Paired benchmarks on macOS on 2026-11-27 gave the results below. The reference executables come from the single-pass compiler, `build/compiler/single/compiler-2`. The candidate executables come from the many-pass compiler, `build/compiler/compiler-2`, whose runtime sets the next old-space collection target to three halves of the bytes that survive a full copy when at least 128 MiB survive.

```sh
sh compiler/bench/run.sh
sh compiler/bench/prover.sh build/compiler/prover-build/prover.input build/export \
    misc/dft-ex build/choice misc/hidden-defpkg-checks/top \
    arithmetic/equalities std/basic/arith-equivs
```

| Workload | Reference seconds | Candidate seconds | Reference peak bytes | Candidate peak bytes |
| --- | ---: | ---: | ---: | ---: |
| Compiler compiling its own input | 0.41 | 0.18 | 35,848,192 | 20,119,552 |
| Checker library check | 23.33 | 13.06 | 352,288,768 | 331,808,768 |
| Calls | 0.01 | 0.00 | 1,081,344 | 1,081,344 |
| Arithmetic | 0.03 | 0.04 | 1,163,264 | 2,146,304 |
| Conses | 0.03 | 0.02 | 5,701,632 | 3,801,088 |
| Strings | 0.01 | 0.00 | 9,486,336 | 1,114,112 |
| Compiler of `compiler/single/` on the prover input | 20.945551 | 8.965209 | 1,314,439,168 | 591,544,320 |
| Prover on `misc/dft-ex` | 258.163250 | 137.074442 | 1,206,419,456 | 1,129,086,976 |
| Prover on `build/choice` | 23.031097 | 13.015923 | 757,858,304 | 641,007,616 |
| Prover on `misc/hidden-defpkg-checks/top` | 26.555251 | 14.857133 | 876,118,016 | 581,615,616 |
| Prover on `arithmetic/equalities` | 73.180912 | 43.919263 | 880,492,544 | 628,129,792 |
| Prover on `std/basic/arith-equivs` | 394.168268 | 206.004227 | 969,342,976 | 794,116,096 |

## Profiles

```sh
sh compiler/bench/profile.sh [-r RUNS] [-s SECONDS] DIR INPUT STDIN
```

profiles the executable that the many-pass compiler writes from `INPUT`, run on `STDIN`, with `sample`, the sampling profiler of macOS. `DIR` is a build directory of `compiler/build.sh` with the certified books up to `compile` in `DIR/acl2/` and the compiler built from them as `DIR/compiler-2`, as `build/compiler` is after `sh compiler/bootstrap.sh`. The executables have no symbols, so ACL2 lays out the items of `INPUT` as the compiler does and writes the offset of every named label (`profile-labels.lsp`); `profile.py` then gives each sample to the label at or before its program counter. It prints the shares of the compiled functions together, of each routine of the runtime, of the collector and of the system calls, and the forty labels with the most samples. Samples in `sys:read` are left out, as the executable waits there for its input while `sample` attaches.

Run on 2026-11-27 with `sh compiler/bench/profile.sh -r 1 -s 120 DIR build/compiler/checker-test/checker.input FRAMED`, where `FRAMED` is the library check of `compiler/README.md` framed by `compiler/frame.sh`, the compiled checker gave 19,221 samples: 49% in compiled code, 33% in the collector (`rt:forward-pointer` alone 17%), 2% in `sys:release`, and 11% outside the executable, in the system. The functions with the most samples were `BOYMOO::APP`, `STRING-CHARS`, `TRIE-CHILD`, `STRING-LINES` and `SUM`, each with 4% to 6%.
