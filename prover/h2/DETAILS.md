# H2 tools and inputs

The commands in [README.md](README.md) start in the repository root.
Programs are found on the `PATH`, and `RUNNER` can name the executable
that evaluates the canonical calls.

| Tool | Use |
|---|---|
| ACL2 through `sh prover/tools/acl2.sh` | Certify H2, run the certified exporter and its readback, or evaluate calls through `acl2-run.sh`. |
| `boymoo-run-fast` or `boymoo-run` | Read terms and evaluate the exported books. The fast runner uses a C compiler when its compiled cache needs a definition. |
| `make` and a C compiler | Build `boymoo-run` when `run.sh` needs a local copy. |
| Node.js through `node` | Run the second checker in the test. |
| `sh`, `awk`, `grep`, `sed`, `cmp`, `cp`, `cat`, `mkdir`, `mv`, `rm`, `wc`, `date` | Build bookkeeping. |
| `timeout` from GNU coreutils | Bound certificate, export, and runner invocations. |

The build reads the certified shared prover books in `build/prover/acl2/`,
the certified exporter in `build/export/acl2/`, and the exported ground
function list in `build/export/ground-fns.lsp`. H2 certificates and exports
live under `build/prover/h2/`.

The run command uses `spec/ground.txt`, `build/export/library.statements`,
`build/export/library.program` and the H2 export. The test is the driver's
(`prover/driver/test.sh`), which reads the exported library and books in
`build/export/`.
