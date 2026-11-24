# Statement information

A statement record is the four-element list `(kind obligation names
package)`. `kind` is a string, such as `"define"` or `"theorem"`.
`obligation` is the printed name requiring a proof entry, or `nil`. `names`
is the list of printed names declared by the statement. `package` is the
decoded package name from a package declaration, or `nil`.

| Function | Arguments and result |
|---|---|
| `(worklist-statement kind obligation names package)` | Constructs the statement record from the four fields above. |
| `(worklist-statement-kind statement)` | The kind of `statement`. |
| `(worklist-statement-obligation statement)` | The obligation name of `statement`, or `nil`. |
| `(worklist-statement-names statement)` | The declared names of `statement`. |
| `(worklist-statement-package statement)` | The decoded package name of `statement`, or `nil`. |
| `(worklist-name-text symbol)` | A reader datum `symbol` as its canonical ASCII text. It propagates a failure from `reader-write`. The datum form is in `prover/sig/reader.md`. |
| `(worklist-recursive definitions)` | Takes a list of definition records, each with its name first and body third. Returns `t` if a body calls any of the defined functions, including inside a lambda body, and `nil` otherwise. A quote is opaque and an `mbe` contributes its logical branch. A missing body or malformed lambda application can give the generic failure. |
| `(worklist-statement-info line)` | Takes one ASCII statement line with an optional terminal line feed. Returns the statement record, propagates a reader failure, or gives the generic failure when a recognized declaration has the wrong form for the worklist. |
