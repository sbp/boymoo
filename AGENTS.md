# Rules for work in this repository

These rules bind every change, whether a person or an agent makes it.

## 1. The repository stands alone

- **It refers to no earlier work.** Nothing in it mentions, quotes, compares with or depends on an earlier version of this project, or on any other work that is not published: no document, code comment, commit message, test or script.
- **It does not tell the story of how something got here.** It says what is so and why. It does not say what was tried, replaced or learned along the way.
- **It names only public things** that a reader can obtain, such as ACL2, the Common Lisp under it, and published papers and systems.

## 2. No path leaves the repository

- **No absolute path** appears anywhere: not in a document, a script, a makefile, a test, or any file that is kept.
- **No path points outside the repository**, whether by `..`, by a home directory, or by a location particular to one machine.
- A tool the work needs, such as ACL2, is found by its name on the `PATH` or is given as an argument. `README.md` lists every such tool.

## 3. Everything is fit to publish

- Write as for a public reader: complete sentences, terms defined before they are used, no private shorthand.
- No personal names, addresses, machine names, account names or credentials.
- No mention of who or what wrote a file, and no note addressed to a collaborator.
- A claim of fact carries what a reader needs to check it: the command in this repository that shows it, and the date it was run.
