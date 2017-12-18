Regexp
======

A regexp matcher, proved correct in the Coq proof assistant.

Requirements
------------

Definitions and proofs:

- [`Coq 8.6.1`](https://coq.inria.fr/coq-86) or [`Coq 8.7`](https://coq.inria.fr/coq-87)
- [`Mathematical Components 1.6.4`](http://math-comp.github.io/math-comp/) (`ssreflect`)
- [`Ott 0.27`](https://github.com/ott-lang/ott) (and its Coq library)
- [`RegLang`](https://github.com/proofengineering/reglang)

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
