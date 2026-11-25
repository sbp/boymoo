# Statement generation

The generator reads statement and aid lines, admits context entries, and
writes a certificate for each obligation it can discharge. The
certificate cache is keyed by the raw statement and retains the context
and auxiliary entries needed for reuse.
