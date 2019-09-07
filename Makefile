OCAMLBUILD = ocamlbuild -use-menhir -tag safe_string -cflag -g

default: Makefile.coq
	+$(MAKE) -f Makefile.coq

install: Makefile.coq
	+$(MAKE) -f Makefile.coq install

matcher: matcher.native

matcher.native: accept.ml accept.mli matcher.ml parser.mly lexer.mll
	$(OCAMLBUILD) matcher.native

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

accept.ml accept.mli: Makefile.coq
	+$(MAKE) -f Makefile.coq $@

clean: Makefile.coq
	+$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf
	$(OCAMLBUILD) -clean

.PHONY: default clean matcher accept.ml accept.mli
.NOTPARALLEL: accept.ml accept.mli
