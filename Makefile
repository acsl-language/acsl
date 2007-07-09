
DEPS=annot1.pp annot2.pp speclang.bnf assigns.pp invariants.pp \
	isqrt.pp incrstar.pp \
	max.pp max_index.pp cond_assigns.pp bsearch.pp \
	listdecl.pp import.pp \
	term.bnf fn_behavior.bnf oldandresult.bnf loc.bnf moreterm.bnf ghost.bnf \
	logic.bnf

all: main.dvi

main.ps: main.dvi
	dvips $^ -o $@

main.dvi: main.tex $(DEPS)
	latex main
	makeindex main
	bibtex main
	latex main
	latex main

%.pp: %.tex pp.ml
	ocaml pp.ml -color $< > $@

%.pp: %.c pp.ml
	ocaml pp.ml -color -c $< > $@

%.bnf: %.tex transf
	./transf < $< > $@

pp.ml: pp.mll
	ocamllex pp.mll

transf: transf.cmo transfmain.cmo
	ocamlc -o $@ $^

%.cmo: %.ml
	ocamlc -c $<

transfmain.cmo: transf.cmo

transf.ml: transf.mll
	ocamllex transf.mll

.PHONY: clean rubber

clean:
	rm -rf *~ *.aux *.log *.nav *.out *.snm *.toc *.pp *.bnf \
               transf trans.ml *.cm?

# see http://www.pps.jussieu.fr/~beffara/soft/rubber/ for details on rubber.
rubber: $(DEPS)
	rubber -d main.tex