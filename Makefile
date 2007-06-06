
DEPS=assigns.pp invariants.pp \
	fn_behavior.bnf loc.bnf term.bnf moreterm.bnf ghost.bnf

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
rubber:
	rubber -d main.tex