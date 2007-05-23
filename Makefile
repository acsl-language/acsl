
all: invariants.pp 

%.pp: pp.ml %.tex 
	ocaml $^ > $@

pp.ml: pp.mll
	ocamllex pp.mll

clean:
	rm -rf *~ *.aux *.log *.nav *.out *.snm *.toc *.pp