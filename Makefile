
all: assigns.pp invariants.pp 

%.pp: %.tex pp.ml
	ocaml pp.ml -color $< > $@

pp.ml: pp.mll
	ocamllex pp.mll

clean:
	rm -rf *~ *.aux *.log *.nav *.out *.snm *.toc *.pp