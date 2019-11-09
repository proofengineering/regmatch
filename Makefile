OCAMLBUILD = ocamlbuild -use-menhir -tag safe_string -cflag -g

default: Makefile.coq
	+$(MAKE) -f Makefile.coq

install: Makefile.coq
	+$(MAKE) -f Makefile.coq install

regexpScript.sml: regexp.ott
	ott -o $@ $<

hol: regexpScript.sml ottScript.sml ottLib.sig ottLib.sml
	Holmake

matcher: matcher.native

matcher.native: accept.ml accept.mli matcher.ml parser.mly lexer.mll
	$(OCAMLBUILD) matcher.native

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

accept.ml accept.mli: Makefile.coq
	+$(MAKE) -f Makefile.coq $@

clean: Makefile.coq
	+$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf regexpScript.sml *Theory.* *.ui *.uo
	$(OCAMLBUILD) -clean

.PHONY: default clean matcher accept.ml accept.mli hol
.NOTPARALLEL: accept.ml accept.mli
