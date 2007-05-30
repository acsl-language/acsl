
all: assigns.pp invariants.pp fn_behavior.bnf loc.bnf term.bnf moreterm.bnf

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

clean:
	rm -rf *~ *.aux *.log *.nav *.out *.snm *.toc *.pp *.bnf \
               transf trans.ml *.cm?