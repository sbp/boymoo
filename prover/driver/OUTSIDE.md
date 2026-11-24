# The host of the prover

The host reads the library, statements and aids as text and passes those
strings to the driver. `driver-prove` returns the proof file as a string
in statement order. `driver-prove-checked` also takes the ground theory as
text, calls the ACL2 Core checker and returns the proof text and verdict.
The host writes the proof bytes and reports the verdict. The command
`sh prover/driver/prove.sh` shows how to quote inputs for the runner and
decode its output. See the [driver signatures](sig/driver.md).

## Clocks and processes

For a search with time limits, the host reads processor and monotonic
clocks. It accounts for set initialization and work on each obligation,
sets the deadlines for attempts and for the input, and reserves time for
checking. `driver-plan` gives the `(rank number set)` triples in order.
Call `driver-attempts` on consecutive pending numbers for one set, or on
one number when it needs an individual limit. Keep each completed
certificate and omit later attempts for its number. The ordinary attempt
allowances of `prove-prover-order` are 2 seconds, or 16 seconds for the
preferred set on a warrant obligation. A host chooses whether to use
these allowances.

A host may begin with three short passes. One policy allocates 0.35,
0.40 and 0.50 of the remaining search time at the start of ranks zero,
one and two. At each attempt, take 80 percent of the time left in that
share divided by the number of pending obligations in the pass. Bound
the resulting processor allowance below by 0.006 seconds and above by
0.08, 0.12 and 0.18 seconds respectively. Begin ordinary attempts at
rank zero. Omit proved obligations and those that exhausted their allowance.

The host starts workers, exchanges requests and replies, reads resource
use and exit status, and interrupts attempts that reach their limits.
Small batches reduce the work lost on a worker exit. Keep completed
replies and omit the current obligation after a worker loss. A timed-out
attempt can leave its obligation eligible while its total allowance
remains. A persistent worker can start a session with `driver-open`,
pass it to `driver-attempt`, and keep the session in each reply. The host
can send only the new suffix when the earlier lines extend those of the
previous request. A host policy may cap certificate replies at 108 MB,
stop active workers at 72 percent of their memory allowance, and retire
idle workers at half their allowance.

## Stored answers

A persistent answer store needs file access and coordination between
writers. Scope answers by set, set version, library and statement text.
Record a completed miss with its exact earlier lines, aids and attempt
budget. A stored certificate can be reused when its dependencies are
available. `cache-subset-dependencies` gives the declaration digests for
its block strings and statement when the host supplies the declaration
indexes. Record refusals with the certificate and the full earlier lines
and aids of the input that refused it. The host can share stored blocks
by their contents.

With automatic orders, the host can look for a usable stored certificate
for each obligation before the first pass. During a pass, consult the
store for the scheduled set and context, and record completed replies
from `driver-attempts`. Supply the retained certificates to
`driver-assemble-answers`.

## Checking collected answers

To check with a separate process, the host writes the text from
`driver-assemble-answers`, starts the checker with the input files, and
reads its verdict and exit status. For a proof or statement rejection,
call `driver-refuse-answers` with the verdict, assemble again and check
the resulting text. For a statement rejection, first check the version
assembled from an empty answer list. Proceed with certificate removal
when that check confirms the skip count. A library rejection or unexpected
checker exit can be reported directly.

The host chooses how to handle a checker resource limit. One policy
drops certificates by descending byte size, using statement order for
ties, until at most half the starting size remains. Get the entries
with `driver-entries-from-answers` and their removal positions with
`prove-prover-checked-halve`, then assemble and check again.

## Testing many inputs

For a library sweep, the host reads the export and stored measures,
chooses the rows and records the result of each case. Give each statement
the library lines that precede it. Use `:library-order` with
`driver-plan`, collect certificates and assemble and check the proof.
Record unproved cases in the ledger as well.

For a book sweep, the host reads the manifest and exports, sets case and
sweep deadlines, and keeps proof files and a ledger so it can resume. Use
`driver-plan` for each book. To reuse an attempt across books, compute the
earlier lines common to the occurrences and pass them followed by the
target to `driver-attempts`. Map the answer back to the target line number
in each book. Assemble and check each proof against its full input before
recording the proved obligations and verdict.
