RegMatch
========

An executable regular expression (regexp) matcher as defined in the paper [Proof-directed debugging revisited](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/educational-pearl-proof-directed-debugging-revisited-for-a-first-order-version/F7CC0A759398A52C35F21F13236C0E00), proved correct in the Coq proof assistant.

Requirements
------------

Definitions and proofs:

- [`Coq 8.9 or later`](https://coq.inria.fr/download)
- [`Mathematical Components 1.7.0 or later`](http://math-comp.github.io/math-comp/) (`ssreflect`)
- [`RegLang`](https://github.com/chdoc/coq-reglang)

Executable matcher:

- [`OCaml 4.02.3`](https://ocaml.org) (or later)
- [`menhir`](http://gallium.inria.fr/~fpottier/menhir/)
- [`OCamlbuild`](https://github.com/ocaml/ocamlbuild)
- [`ocamlfind`](https://ocaml.org)

Building
--------

One easy way to install the dependencies (ssreflect, RegLang, and menhir) is via [OPAM](http://opam.ocaml.org/doc/Install.html):
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install menhir coq-mathcomp-ssreflect coq-reglang
```

Then, run `make`. This will compile the Coq syntax and relation definitions along with the proofs and functions, and extract OCaml code.

To build the executable matcher program, run `make matcher`.
