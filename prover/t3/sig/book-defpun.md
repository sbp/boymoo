# Stopping-time recursion

The Library, Step, term and entry representations are those in
`prover/sig/library.md` and `prover/sig/proof.md`. Evidence and bindings preserve
the order in which the proof recipe supplies them.

The constants `*t3-book-defpun-step*`, `*t3-book-defpun-test*`,
`*t3-book-defpun-base*`, `*t3-book-defpun-iterate*`,
`*t3-book-defpun-bounded*`, `*t3-book-defpun-result*`,
`*t3-book-defpun-choose*`, `*t3-book-defpun-n*`, `*t3-book-defpun-m*` and
`*t3-book-defpun-agreement*` are prover symbols. The result constant names
`DEFPUN-F`.

| Call | Arguments and result | Failure |
| --- | --- | --- |
| `(t3-book-defpun-recursion-equation state)` | State term. Returns the equation for one step of the recursion. | None. |
| `(t3-book-defpun-defpun lib name formula)` | Library, theorem name symbol and recursion equation term. Returns `(cons entry lib)` with the theorem entry and the Library containing the auxiliary agreement lemma. | A failure from reading the equation or building the proof. |
| `(t3-book-defpun-iteration-test state clock)` | State and clock terms. Returns the stopping test after the given number of iterations. | None. |
| `(t3-book-defpun-open-under lib call evidence)` | Library, call term and list of evidence Steps. Returns the unfolded and normalized equation Step. | A failure from building the proof. |
| `(t3-book-defpun-conjunction lib first second)` | Library and two Steps. Returns the Step proving their conjunction. | A failure from building the proof. |
| `(t3-book-defpun-terminal-result lib state clock stopped)` | Library, state and clock terms, and stopping Step. Returns the Step for the terminal value of the bounded recursion. | A failure from building the proof. |
| `(t3-book-defpun-impossible lib contradiction goal)` | Library, contradiction Step and goal term. Returns the Step with the goal added to the clause. | A failure from building the proof. |
| `(t3-book-defpun-agreement lib)` | Library. Returns the Library with the bounding agreement lemma. | A failure from building the proof. |
| `(t3-book-defpun-agreement-zero clock proof lib x waiting goal)` | Clock term, stopping Step, Library, state term, waiting Step and goal term. Returns the zero-clock case Step for agreement. | A failure from building the proof. |
| `(t3-book-defpun-agreement-forward clock reached-at positive lib x)` | Clock term, stopping Step, nonzero-clock Step, Library and state term. Returns the Step for stopping after one iteration. | A failure from building the proof. |
| `(t3-book-defpun-chosen lib state clock stops)` | Library, state and clock terms, and stopping Step. Returns the Step establishing that the chosen clock stops. | A failure from building the proof. |
| `(t3-book-defpun-preceding-clock lib state clock later positive)` | Library, state and clock terms, stopping Step for the next state, and Boolean nonzero-clock flag. Returns the Step establishing a stopping clock at the current state. | A failure from building the proof. |
