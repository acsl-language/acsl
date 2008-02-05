
DEPS=intro.tex speclang.tex libraries.tex compjml.tex \
	div_lemma.pp assigns.pp invariants.pp example-lt.pp \
	isqrt.pp incrstar.pp parsing_annot.pp integer-cast.pp \
	max.pp max_index.pp cond_assigns.pp bsearch.pp bsearch2.pp \
	assigns_array.pp assigns_list.pp sum.pp \
	listdecl.pp listdef.pp listlengthdef.pp import.pp listmodule.pp \
	strcpyspec.pp dowhile.pp num_of_pos.pp nb_occ.pp permut.pp \
	acsl_allocator.pp gen_spec_with_model.pp gen_code.pp out_char.pp \
	ghostpointer.pp ghostcfg.pp flag.pp lexico.pp footprint.pp \
	fwrite-malloc.pp loopvariantnegative.pp \
	fact.pp mutualrec.pp abrupt_termination.pp \
        advancedloopinvariants.pp inductiveloopinvariants.pp \
	term.bnf binders.bnf fn_behavior.bnf oldandresult.bnf at.bnf loc.bnf \
	assertions.bnf loops.bnf generalinvariants.bnf \
	st_contracts.bnf moreterm.bnf ghost.bnf \
	logic.bnf logictypedecl.bnf higherorder.bnf logicreads.bnf \
	data_invariants.bnf  \
	cfg.mps

all: main.pdf

main.ps: main.dvi
	dvips $^ -o $@

main.dvi: main.tex $(DEPS)
	latex main
	makeindex main
	bibtex main
	latex main
	latex main

main.pdf: main.tex $(DEPS)
	pdflatex main
	makeindex main
	bibtex main
	pdflatex main
	pdflatex main

%.1: %.mp
	mpost -interaction batchmode $<

%.mps: %.1
	mv $< $@

%.pp: %.tex pp
	./pp -utf8 $< > $@

%.pp: %.c pp
	./pp -utf8 -c $< > $@

%.bnf: %.tex transf
	./transf < $< > $@

%.ml: %.mll
	ocamllex $<

pp: pp.ml
	ocamlopt -o $@ $^

transf: transf.cmo transfmain.cmo
	ocamlc -o $@ $^

%.cmo: %.ml
	ocamlc -c $<

transfmain.cmo: transf.cmo

.PHONY: clean rubber

check:
	gcc -c *.c
	for f in *.c ; do ../../bin/toplevel.byte $$f ; done

clean:
	rm -rf *~ *.aux *.log *.nav *.out *.snm *.toc *.pp *.bnf \
               transf trans.ml *.cm?

# see http://www.pps.jussieu.fr/~beffara/soft/rubber/ for details on rubber.
rubber: $(DEPS)
	rubber -d main.tex