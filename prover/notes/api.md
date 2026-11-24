# Preparing an obligation

The public API normalizes lines, reads the selected statement and
prepares its proof context from the supplied library and earlier
lines. The context keeps declared and auxiliary names distinct.
Input already present in the context needs no duplicate proof.

For recursive definitions the API tries the supplied measure and
the ordered candidate measures. A successful certificate supplies
its prerequisite entries and the statement's proof entry.
