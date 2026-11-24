# Statement information

`worklist-statement-info` uses the shared reader to read the first datum of
a theorem, axiom, choice, reservation, or package declaration. It reads a
definition group or constraint in full and removes one terminal line feed
before parsing. It spells names with `reader-write` and keeps the decoded
package name as a field of the statement record.

`worklist-recursive` searches the bodies for calls to any member of a
definition group. It visits lambda bodies and application arguments, treats
quoted data as opaque, and follows the logical branch of `mbe`. Recursive
definition groups and constraints with formulas use the first defined name
as their obligation. The protection flag records whether any member of a
definition group belongs to `COMMON-LISP`.
