COQVERSION := $(shell coqc --version|egrep "version (8\\.5|8\\.6)")
ifeq "$(COQVERSION)" ""
$(error "Only compatible with Coq version 8.5 or 8.6")
endif

COQPROJECT_EXISTS = $(wildcard _CoqProject)
ifeq "$(COQPROJECT_EXISTS)" ""
$(error "Run ./configure before running make")
endif

OCAMLBUILD = ocamlbuild -use-menhir -tag safe_string -cflag -g
OTT = ott
PDFLATEX = pdflatex

OTTFILES = regexp.ott
VFILES = $(OTTFILES:.ott=.v)
TEXFILES = $(OTTFILES:.ott=.tex)
PDFFILES = $(TEXFILES:.tex=.pdf)

MLFILES = accept.ml accept.mli

default: Makefile.coq
	$(MAKE) -f Makefile.coq

matcher.native: $(MLFILES) matcher.ml
	$(OCAMLBUILD) matcher.native

Makefile.coq: $(VFILES)
	coq_makefile -f _CoqProject -o Makefile.coq -no-install \
          -extra '$(MLFILES)' \
            'accept_extrocaml.v regexp_metatheory.vo' \
            '$$(COQC) $$(COQDEBUG) $$(COQFLAGS) accept_extrocaml.v'

$(VFILES): %.v: %.ott
	$(OTT) -o $@ -coq_expand_list_types false $<

$(MLFILES): Makefile.coq
	$(MAKE) -f Makefile.coq $@

$(TEXFILES): %.tex: %.ott
	$(OTT) -o $@ $<

$(PDFFILES): $(TEXFILES)
	$(PDFLATEX) $<
	$(PDFLATEX) $<

clean:
	if [ -f Makefile.coq ]; then \
	  $(MAKE) -f Makefile.coq cleanall; fi
	rm -f Makefile.coq $(VFILES)
	$(OCAMLBUILD) -clean

.PHONY: default clean
.NOTPARALLEL: $(MLFILES)
