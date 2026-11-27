# Boymoo

**Boymoo** is an independent implementation of a subset of [ACL2](https://en.wikipedia.org/wiki/ACL2).

ACL2 is a proof assistant in the [Boyer-Moore family](https://en.wikipedia.org/wiki/Nqthm), written in Common Lisp. It allows you to state mathematical conjectures, which can include properties of computer programs, and then assists you in writing a proof.

Unlike many other well known proof assistants, ACL2 does not produce a [machine checkable version](https://en.wikipedia.org/wiki/De_Bruijn_criterion) of the proof. Boymoo provides a way to make proofs of ACL2 theorems checkable, and the Boymoo checker itself is written in a subset of ACL2 called ACL2 Core.

The advantages of Boymoo, therefore, are that it provides an independent second opinion on whether ACL2 theorems are correct, and that it does so in a way which can be checked automatically by a machine. In addition, it has an entirely independent runtime written in just a couple of thousand lines of ISO C99 instead of Common Lisp, and compilers written in ACL2 Core targeting aarch64.

## Terminology

The main components of Boymoo are written in ACL2, ACL2 Core, C, and JavaScript. ACL2 is the normal language that people write when using the ACL2 system, but internally everything is expressed in a set of events, primitives, and some builtins, which together constitute a subset of ACL2 which is referred to here as ACL2 Core.

In ACL2, theorems are grouped together in what in most languages are called packages or modules, but in ACL2 are called [books](https://www.cs.utexas.edu/~moore/acl2/v8-7/combined-manual/?topic=ACL2____BOOKS). Books are written in ACL2, not ACL2 Core, but the language that Boymoo implements is ACL2 Core alone. This is reflected in the components.

## Components

There are several components in Boymoo, listed below with the language in which they are implemented, and their current status.

Completed:

* Book exporter (**ACL2**): converts ACL2 books to ACL2 Core.
* Bootstrap runner (**C**): small, and about 10x slower than ACL2 using SBCL.
* Fast runner (**C**): large, and compiles to C, but faster than the Bootstrap runner. Only intended for development of the "Prover", below.
* Checker (**ACL2 Core**): checks proofs of ACL2 Core.
* Independent checker (**JavaScript**): checks proofs of ACL2 Core.
* Prover (**ACL2 Core**): assists with building proofs of ACL2 Core conjectures.
* Compiler for aarch64 (**ACL2 Core**): compiles an ACL2 Core program into machine code, supporting Linux and macOS, through many passes over intermediate languages. A single-pass compiler beside it compiles it first, and is the reference that its executables are compared with.

Yet to do:

* Compiler for other architectures (**ACL2 Core**): compiles an ACL2 Core program into machine code, adding potential support for WASM, RV64I + Zmmul, and x64.
* POSIX interface (**ACL2 Core, C**): potential way to drive I/O and devices using ACL2 Core programs.

The components that are implemented in ACL2 or ACL2 Core can have proofs written to prove certain correctness properties about them. These are in varying states of completion; see the rest of the repository for details.

## Limitations

Because the book exporter is written in ACL2, not in ACL2 Core, it requires ACL2 and Common Lisp to run it. The book exporter is a way to bridge existing definitions and theorems written in ACL2 with Boymoo, by converting them to ACL2 Core format.

## Status

Boymoo is a prototype, not intended for production use. Please report all bugs, including soundness bugs, in public on the GitHub issue tracker. No claims whatsoever are made about the security or correctness of this system.

This is open source software maintained by volunteers. No support is offered, and even responses on issue threads cannot be guaranteed. You are equally a volunteer, and are therefore equally responsible for helping to resolve issues and to make contributions. Professional quality audits would be very gratefully received, if donated free of charge.

The authors of ACL2 do not endorse, and likely do not even know about the existence of, Boymoo. Please _do not_ send bug reports or feature requests about Boymoo to the ACL2 maintainers, or vice versa. The two are entirely separate, independent projects.

Boymoo currently tracks the features and specification of ACL2 8.7.

## Background

But why do all of this?

Aside from the fact that ACL2 is a very interesting and unique system with many years of talented engineering behind it, different proof assistants have always provided different tradeoffs. Some have small kernels, some don't. Some are computational, some aren't. There are many such choices and characteristics, and ACL2 made some unusual choices. For example, it is untyped, whereas many of the most well known proof assistants are typed. It is also first order, meaning that functions cannot be used as arguments, which is again a somewhat unusual choice.

Tradeoffs, by their nature, rebalance advantages and disadvantages. Being first order, for example, has the disadvantage of losing some expressivity, but the advantage of making proofs easier to generate automatically. Even in 2026 this can be an advantage, because it helps to keep costs and resource usage down.

In summary, then, the set of choices made by ACL2 are attractive for some use cases. But some of the disadvantages that ACL2 incurs, such as requiring a whole Common Lisp implementation even to run code and not having machine checkable proofs, could only be fixed by a new implementation, as alluded to in the introduction. Boymoo was therefore written to test these ideas, and to provide inspiration and direction as to what the next generation of Boyer-Moore proof assistants may look like.

## License

Licensed under MIT-0. Share and enjoy!
