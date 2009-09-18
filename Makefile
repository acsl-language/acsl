MAIN=main
DEPS_MODERN=speclang_modern.tex macros_modern.tex                       \
	intro_modern.tex libraries_modern.tex compjml_modern.tex        \
	div_lemma.c assigns.c invariants.c		                \
	example-lt-modern.tex isqrt.c sizeof.c incrstar.c		\
	parsing_annot_modern.tex integer-cast-modern.tex max.c		\
	max_index.c cond_assigns.c bsearch.c bsearch2.c			\
	assigns_array.c assigns_list.c sum.c listdecl.c listdef.c	\
	listlengthdef.c import.c listmodule.c strcpyspec.c dowhile.c	\
	num_of_pos.c nb_occ.c nb_occ_reads.c permut.c permut_reads.c	\
	acsl_allocator.c gen_spec_with_model.c gen_code.c out_char.c	\
	ghostpointer.c ghostcfg.c flag.c lexico.c footprint.c		\
	loopvariantnegative.c fact.c mutualrec.c abrupt_termination.c	\
	advancedloopinvariants.c inductiveloopinvariants_modern.tex	\
	term_modern.bnf binders_modern.bnf fn_behavior_modern.bnf	\
	oldandresult_modern.bnf at_modern.bnf loc_modern.bnf		\
	assertions_modern.bnf loops_modern.bnf				\
	generalinvariants_modern.bnf st_contracts_modern.bnf		\
	moreterm_modern.bnf ghost_modern.bnf model_modern.bnf		\
	logic_modern.bnf inductive_modern.bnf logicdecl_modern.bnf	\
	logictypedecl_modern.bnf higherorder_modern.bnf			\
	logiclabels_modern.bnf logicreads_modern.bnf			\
	data_invariants_modern.bnf cfg.mps volatile.c			\
	volatile-gram_modern.bnf euclide.c initialized.c specified.c	\
	exitbehavior_modern.bnf dependencies_modern.bnf sum2.c		\
	modifier.c gen_spec_with_ghost.c terminates_list.c		\
	glob_var_masked.c glob_var_masked_sol.c intlists.c sign.c	\
	signdef.c oldat.c mean.c isgcd.c exit.c mayexit.c

.PHONY: all install acsl tutorial

acsl: acsl-implementation.pdf acsl.pdf main.pdf

all: acsl install tutorial check

tutorial: tutorial-check acsl-mini-tutorial.pdf acsl-mini-tutorial.html

install: acsl-implementation.pdf acsl.pdf
	cp -f acsl-implementation.pdf acsl.pdf ../manuals/

include ../MakeLaTeXModern

%.1: %.mp
	mpost -interaction batchmode $<

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
	pdflatex $<
	bibtex $(<:.tex=)
	pdflatex $<
	pdflatex $<

pp: pp.ml
	ocamlopt -o $@ str.cmxa $^

transf: transf.cmo transfmain.cmo
	ocamlc -o $@ $^

%.cmo: %.ml
	ocamlc -c $<

transfmain.cmo: transf.cmo

.PHONY: check tutorial-check

check:
	gcc -c -std=c99 *.c
	for f in *.c ; do ../../bin/toplevel.byte -pp-annot $$f ; done

tutorial-check: acsl-mini-tutorial.tex
	@for f in *-tut.c; do \
            echo "***Starting analysis of $$f"; \
            gcc -c -std=c99 $$f; \
            ../../bin/toplevel.byte -pp-annot $$f; \
        done

acsl-mini-tutorial.pdf: acsl-mini-tutorial.tex mini-biblio.bib
	pdflatex acsl-mini-tutorial
	bibtex acsl-mini-tutorial
	pdflatex acsl-mini-tutorial
	pdflatex acsl-mini-tutorial

acsl-mini-tutorial.html: acsl-mini-tutorial.tex mini-biblio.bib
	hevea acsl-mini-tutorial.tex
	bibhva acsl-mini-tutorial
	hevea -fix acsl-mini-tutorial.tex

.PHONY: clean

clean:
	rm -rf *~ *.aux *.log *.nav *.out *.snm *.toc *.lof *.pp *.bnf \
		*.haux  *.hbbl *.htoc \
                *.cb *.cm? *.bbl *.blg *.idx *.ind *.ilg \
		transf trans.ml pp.ml pp

# version WEB liée à ce qui est implementé
acsl-implementation.pdf: $(DEPS_MODERN) $(FRAMAC_MODERN)

acsl-implementation.tex: $(MAIN).tex
	rm -f $@
	sed -e '/PrintRemarks/s/%--//' $^ > $@
	chmod a-w $@

# version WEB du langage ACSL
acsl.pdf: $(DEPS_MODERN) $(FRAMAC_MODERN)

acsl.tex: acsl-implementation.tex
	rm -f $@
	sed -e '/PrintImplementationRq/s/%--//' $^ > $@
	chmod a-w $@

# version pour le goupe de travail ACSL
$(MAIN).pdf: $(DEPS_MODERN) $(FRAMAC_MODERN)

%.pdf: %.tex
	pdflatex $*
	makeindex $*
	bibtex $*
	pdflatex $*
	pdflatex $*

# Command to produce a diff'ed document. Must be refined to flatten automatically the files
# latexdiff --type=CFONT --append-textcmd="_,sep,alt,newl,is" --append-safecmd="term,nonterm,indexttbase,indextt,indexttbs,keyword,ensuremath" --config "PICTUREENV=(?:picture|latexonly)[\\w\\d*@]*,MATHENV=(?:syntax),MATHREPL=syntax"  full.tex current/full.tex > diff.tex
