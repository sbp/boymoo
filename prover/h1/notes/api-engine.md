# Statement worlds and proof export

A world holds the prover, the lines already admitted, and the names
declared by those lines. Each proof attempt starts from the world for
its supplied library and prefix. Input normalization accepts a list of
lines or a string containing line breaks. A carriage return followed by
a newline is one line terminator.

Export selects the entries needed by the conclusion in dependency order.
A definition and its measure stay together. Export assigns the generated
names using the full SipHash-2-4 digest of the auxiliary group text, a
zero character, and the name being replaced. It applies names already
assigned to dependencies before computing the group's digest.
