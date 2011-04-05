MAIN=main
DEPS_MODERN=macros_modern.tex framacversion.tex biblio.bib \
	intro_modern.tex speclang_modern.tex \
	libraries_modern.tex concl_modern.tex \
	term_modern.bnf binders_modern.bnf predicate_modern.bnf \
	fn_behavior_modern.bnf oldandresult_modern.bnf \
	loc_modern.bnf \
	assertions_modern.bnf loops_modern.bnf st_contracts_modern.bnf \
	logic_modern.bnf data_invariants_modern.bnf model_modern.bnf \
	ghost_modern.bnf generalinvariants_modern.bnf iterator_modern.bnf \
	bsearch.c bsearch2.c link.c

.PHONY: all e-acsl default

default: e-acsl.pdf

e-acsl: e-acsl-implementation.pdf e-acsl.pdf main.pdf

all: e-acsl

# install: acsl-implementation.pdf acsl.pdf
# 	cp -f acsl-implementation.pdf acsl.pdf ../manuals/

include ../../MakeLaTeXModern

framacversion.tex: ../../../VERSION Makefile
	rm -f $@
	printf '\\newcommand{\\framacversion}{' > $@
	cat $< >> $@
	echo '}' >> $@
	chmod a-w $@

%.1: %.mp
	mpost -interaction=batchmode $<

%.mps: %.1
	mv $< $@

%.pp: %.tex pp
	./pp -utf8 $< > $@

%.pp: %.c pp
	./pp -utf8 -c $< > $@

%.tex: %.ctex pp
	rm -f $@
	./pp $< > $@
	chmod a-w $@

%.bnf: %.tex transf
	rm -f $@
	./transf $< > $@
	chmod a-w $@

%_modern.bnf: %.tex transf
	rm -f $@
	./transf -modern $< > $@
	chmod a-w $@

%.ml: %.mll
	ocamllex $<

%.pdf: %.tex
	pdflatex $*
	makeindex $*
	bibtex $*
	pdflatex $*
	pdflatex $*

%.cmo: %.ml
	ocamlc -c $<

pp: pp.ml
	ocamlopt -o $@ str.cmxa $^

transf: transf.cmo transfmain.cmo
	ocamlc -o $@ $^

transfmain.cmo: transf.cmo

.PHONY: clean

clean:
	rm -rf *~ *.aux *.log *.nav *.out *.snm *.toc *.lof *.pp *.bnf \
		*.haux  *.hbbl *.htoc \
                *.cb *.cm? *.bbl *.blg *.idx *.ind *.ilg \
		transf trans.ml pp.ml pp

# version WEB liée à ce qui est implementé
e-acsl-implementation.pdf: $(DEPS_MODERN)

e-acsl-implementation.tex: $(MAIN).tex Makefile
	rm -f $@
	sed -e '/PrintRemarks/s/%--//' $^ > $@
	chmod a-w $@

# version WEB du langage ACSL
e-acsl.pdf: $(DEPS_MODERN)

e-acsl.tex: e-acsl-implementation.tex Makefile
	rm -f $@
	sed -e '/PrintImplementationRq/s/%--//' $^ > $@
	chmod a-w $@

# version pour le goupe de travail ACSL
$(MAIN).pdf: $(DEPS_MODERN)
