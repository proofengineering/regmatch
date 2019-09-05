RegMatch
========

An executable regular expression (regexp) matcher as defined in the paper [Proof-directed debugging revisited](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/educational-pearl-proof-directed-debugging-revisited-for-a-first-order-version/F7CC0A759398A52C35F21F13236C0E00), proved correct in the Coq proof assistant.

Requirements
------------

Definitions and proofs:

- [`Coq 8.9 or later`](https://coq.inria.fr/download)
- [`Mathematical Components 1.8.0 or later`](http://math-comp.github.io/math-comp/) (`ssreflect`)
- [`Ott 0.29`](https://github.com/ott-lang/ott) (and its Coq library)
- [`RegLang`](https://github.com/chdoc/coq-reglang)

Executable matcher:

- [`OCaml 4.02.3`](https://ocaml.org) (or later)
- [`menhir`](http://gallium.inria.fr/~fpottier/menhir/)
- [`OCamlbuild`](https://github.com/ocaml/ocamlbuild)
- [`ocamlfind`](https://ocaml.org)

Building
--------

Make sure the `ott` program is in the `PATH`, and Ott's Coq auxiliary library has been installed under Coq's `user-contrib` directory. Also make sure the RegLang Coq library has been installed.

One easy way to install ssreflect, RegLang, as well as Ott and its Coq library is via [OPAM](http://opam.ocaml.org/doc/Install.html):
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install ott coq-mathcomp-ssreflect coq-reglang coq-ott
```

Then, run `make`. This will compile the Coq syntax and relation definitions along with the proofs and functions, and extract OCaml code.

To build the executable matcher program, run `make matcher`.
