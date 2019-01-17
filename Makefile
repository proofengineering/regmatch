include Makefile.detect-coq-version

include Makefile.ml-files

ifeq (,$(filter $(COQVERSION),8.5 8.6 8.7 8.8 8.9 8.10 dev))
$(error "only compatible with Coq version 8.5 or later")
endif

COQPROJECT_EXISTS := $(wildcard _CoqProject)
ifeq "$(COQPROJECT_EXISTS)" ""
$(error "Run ./configure before running make")
endif

OCAMLBUILD = ocamlbuild -use-menhir -tag safe_string -cflag -g
OTT = ott
PDFLATEX = pdflatex

OTTFILES = regexp.ott
TEXFILES = $(OTTFILES:.ott=.tex)
PDFFILES = $(TEXFILES:.tex=.pdf)

default: Makefile.coq
	$(MAKE) -f Makefile.coq

matcher: matcher.native

matcher.native: $(ACCEPTML) matcher.ml parser.mly lexer.mll
	$(OCAMLBUILD) matcher.native

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

$(ACCEPTML): Makefile.coq
	$(MAKE) -f Makefile.coq $@

$(TEXFILES): %.tex: %.ott
	$(OTT) -o $@ $<

$(PDFFILES): $(TEXFILES)
	$(PDFLATEX) $<
	$(PDFLATEX) $<

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf parser.v
	$(OCAMLBUILD) -clean

.PHONY: default clean matcher $(ACCEPTML)
.NOTPARALLEL: $(ACCEPTML)
