Regexp
======

A regexp matcher as defined in the paper [Proof-directed debugging revisited](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/educational-pearl-proof-directed-debugging-revisited-for-a-first-order-version/F7CC0A759398A52C35F21F13236C0E00), proved correct in the Coq proof assistant.

Requirements
------------

Definitions and proofs:

- [`Coq 8.7`](https://coq.inria.fr/coq-87) or [`Coq 8.8`](https://coq.inria.fr/download)
- [`Mathematical Components 1.6.4 or 1.7.0`](http://math-comp.github.io/math-comp/) (`ssreflect`)
- [`Ott 0.28`](https://github.com/ott-lang/ott) (and its Coq library)
- [`RegLang`](https://github.com/chdoc/coq-reglang)

Executable matcher:

- [`OCaml 4.02.3`](https://ocaml.org) (or later)
- [`menhir`](http://gallium.inria.fr/~fpottier/menhir/)
- [`OCamlbuild`](https://github.com/ocaml/ocamlbuild)
- [`ocamlfind`](https://ocaml.org)

Building
--------

Make sure the `ott` program is in the `PATH`, and Ott's Coq auxiliary library has been installed under Coq's `user-contrib` directory (default) or set the `Ott_PATH` environment variable to an alternative location. One easy way to install Ott and its Coq library is via [OPAM](http://opam.ocaml.org/doc/Install.html):
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install ott coq-ott
```

Then, run `./configure`, followed by `make`. This will compile the Coq syntax and relation definitions along with the proofs and functions, and extract OCaml code.
