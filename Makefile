default: acsl.pdf

MAIN=main

PDF_OUTPUTS=acsl-implementation.pdf acsl.pdf acslpp-implementation.pdf acslpp.pdf

## Notes:
## no longer built target: acsl-mini-tutorial.pdf
## PDF_OUTPUTS are copied to "../manuals" directory bg "install" target

BNF_FILES=term.tex predicate.tex binders.tex fn_behavior.tex \
          oldandresult.tex at.tex loc.tex assertions.tex loops.tex  \
          assertions.tex loops.tex allocation.tex generalinvariants.tex \
          st_contracts.tex ghost.tex model.tex logic.tex inductive.tex \
          logicdecl.tex logictypedecl.tex higherorder.tex logiclabels.tex \
          logicreads.tex memory.tex initialized.tex data_invariants.tex volatile-gram.tex \
          exitbehavior.tex dependencies.tex welltyped.tex list-gram.tex \
          c-type-name.tex \
          cpp-exceptionbehavior.tex cpp-default-values-syntax.tex \
          cpp-class-invariants-fig.tex cpp-this.tex cpp-gram-pure.tex

BNF_DEPS=$(BNF_FILES:.tex=.bnf)

DEPS= main.tex speclang_modern.tex macros_modern.tex intro_modern.tex		\
	libraries_modern.tex compjml_modern.tex div_lemma.c assigns.c	\
	invariants.c example-lt-modern.tex biblio.bib			\
	malloc_free_fn.c malloc-free2-fn.c loop-frees.c isqrt.c		\
	sizeof.c incrstar.c parsing_annot_modern.tex			\
	integer-cast-modern.tex max.c max_index.c cond_assigns.c	\
	bsearch.c bsearch2.c assigns_array.c assigns_list.c sum.c	\
	listdecl.c listdef.c listlengthdef.c import.c listmodule.c	\
	strcpyspec.c dowhile.c num_of_pos.c nb_occ.c nb_occ_reads.c	\
	permut.c permut_reads.c acsl_allocator.c			\
	gen_spec_with_model.c gen_code.c out_char.c ghostpointer.c	\
	ghostcfg.c flag.c lexico.c footprint.c loopvariantnegative.c	\
	fact.c mutualrec.c abrupt_termination.c				\
	advancedloopinvariants.c inductiveloopinvariants_modern.tex	\
	$(BNF_DEPS) cfg.mps volatile.c euclide.c initialized.c		\
	dangling.c sum2.c modifier.c gen_spec_with_ghost.c		\
	terminates_list.c glob_var_masked.c glob_var_masked_sol.c	\
	intlists.c sign.c signdef.c oldat.c mean.c isgcd.c exit.c	\
	mayexit.c loop_current.c welltyped.c list-observer.c            \
	Makefile VERSION

DEPS_CPP= acslpp.tex acslpp-implementation.tex cpp-abstraction.tex cpp-attributes.tex \
    cpp-auto.tex cpp-class-contracts.tex cpp-class-invariants.tex \
    cpp-default-values.tex cpp-defensive.tex cpp-enum.tex \
    cpp-exceptions.tex cpp-foreword.tex cpp-forrange.tex \
    cpp-functional-design.tex cpp-functional-examples.tex \
    cpp-functional.tex cpp-invariants.tex cpp-main.tex \
	cpp-namespaces.tex cpp-preprocessing.tex  \
    cpp-templates.tex cpp-types.tex cpp-type.tex cpp-visibility.tex

TUTORIAL_EXAMPLES=max_ptr-tut.c max_ptr2-tut.c max_ptr_bhv-tut.c \
                  max_seq_ghost-tut.c

.PHONY: all install acsl tutorial

%.1: %.mp
	mpost -interaction=batchmode $<

%.mps: %.1
	mv $< $@

%.pp: %.tex pp
	./pp -utf8 $< > $@

%.pp: %.c pp
	./pp -utf8 -c $< > $@

%.tex: %.ctex pp
	@rm -f $@
	./pp $< > $@
	@chmod a-w $@

%.bnf: %.tex transf
	@rm -f $@
	./transf $< > $@
	@chmod a-w $@

%.ml: %.mll
	ocamllex $<

.PHONY: main.pdf
main.pdf:
	@echo "Deprecated '$@' target:"
	@echo "please, make 'acsl-implementation.pdf' or else 'acsl.pdf'"

%.pdf: %.tex $(DEPS) $(BNF_DEPS)
	latexmk -silent -pdf $<

pp: pp.ml
	ocamlopt -o $@ str.cmxa $^

transf: transf.cmo transfmain.cmo
	ocamlc -o $@ $^

%.cmo: %.ml
	ocamlc -c $<

%.proved:%.c acsl-mini-tutorial.tex
	$(FRAMAC) -wp $<
	touch $@

%.check: %.c acsl-mini-tutorial.tex
	$(FRAMAC) $<

transfmain.cmo: transf.cmo

# Internal to Frama-C
FRAMAC ?= ../../bin/frama-c

HAS_FRAMAC:=$(shell if test -x $(FRAMAC); then echo yes; else echo no; fi)

.PHONY: full-check check tutorial-check grammar-check
full-check: check tutorial-check grammar-check

ifneq ("$(HAS_FRAMAC)","yes")

.PHONY: cannot-check
cannot-check:
	@echo "check targets can only be made within Frama-C sources"
	@exit 2

tutorial-check: cannot-check
check: cannot-check

else
GOOD=abrupt_termination.c advancedloopinvariants.c assert-tut.c		\
assigns_array.c assigns.c assigns_list.c bsearch.c bsearch2.c		\
cond_assigns.c div_lemma.c dowhile.c euclide.c exit.c extremum-tut.c	\
extremum2-tut.c fact.c flag.c footprint.c ghostpointer.c		\
glob_var_masked.c glob_var_masked_sol.c global_invariant-tut.c		\
incrstar.c initialized.c intlists.c isgcd.c isqrt.c listdecl.c		\
listdef.c loopvariantnegative.c loop-frees.c loop_current.c             \
malloc_free_fn.c malloc-free2-fn.c 					\
max-tut.c max.c max_index.c	        				\
max_list-tut.c max_ptr-tut.c max_ptr2-tut.c max_ptr_bhv-tut.c		\
max_ptr_false-tut.c max_seq-tut.c max_seq2-tut.c max_seq_assigns-tut.c	\
max_seq_ghost-tut.c max_seq_inv-tut.c max_seq_old-tut.c			\
max_seq_old2-tut.c mayexit.c mean.c minitutorial.c mutualrec.c		\
nb_occ.c nb_occ_reads.c non_terminating-tut.c non_terminating2-tut.c	\
num_of_pos.c oldat.c permut.c permut_reads.c sizeof.c sign.c signdef.c	\
sort.c specified.c sqsum-tut.c sqsum2-tut.c strcpyspec.c sum.c          \
swap-tut.c terminates_list.c type_invariant-tut.c volatile.c dangling.c \
welltyped.c list-observer.c

BAD=acsl_allocator.c gen_code.c gen_spec_with_ghost.c			\
gen_spec_with_model.c ghostcfg.c import.c invariants.c			\
lexico.c listlengthdef.c listmodule.c                                   \
modifier.c out_char.c sum2.c

check: acsl-mini-tutorial.tex
	gcc -c -std=c99 *.c -Wall
	@good=0; \
        bad=0; \
        failed=0; \
        passed=0; \
	failed_list=""; \
        passed_list=""; \
        for f in *.c ; do \
	  echo "considering $$f"; \
	  if test `grep -c "NOPP-END." $$f` -ne 0 ; then \
	    echo "Failure since NOPP-END should end the line: $$f"; \
	    exit 1; \
	  fi; \
          $(FRAMAC) -pp-annot -verbose 0 $$f ; \
          case $$? in \
            0) if echo "$(GOOD)" | grep -q -e "$$f"; then good=$$(($$good +1)); \
               else passed=$$(($$passed+1)); \
                    passed_list="$$passed_list $$f"; \
	       fi;; \
            *) if echo "$(BAD)" | grep -q -e "$$f"; then bad=$$(($$bad + 1)); \
               else failed=$$(($$failed+1)); \
                    failed_list="$$failed_list $$f"; \
               fi;; \
          esac; \
        done; \
	echo "$$good examples passed, $$bad failed as expected"; \
	if test $$failed -ne 0 -o $$passed -ne 0; then \
	  echo "$$failed examples failed, $$passed unexpectedly passed."; \
          echo "Failures: $$failed_list"; \
          echo "Accepted: $$passed_list"; \
          exit 1; \
        fi

# On the contrary to check above, all files in the tutorial are supposed to
# be supported by Frama-C
tutorial-check: acsl-mini-tutorial.tex
	@failed=0; \
         failed_list=""; \
          for f in *-tut.c; do \
            gcc -c -std=c99 $$f; \
            $(FRAMAC) -pp-annot -verbose 0 $$f; \
	    if test $$? -ne 0; then \
              failed=$$(($$failed + 1)); \
              failed_list="$$failed_list $$f"; \
            fi; \
        done; \
        if test $$failed -ne 0; then \
	   echo "$$failed tests from the tutorial failed."; \
           echo "Failures: $$failed_list"; \
	   exit 1; \
        else echo "All examples from the tutorial are accepted. Good!"; \
        fi

BUILTINS=real integer string character id \
         function-contract global-invariant type-invariant logic-specification \
         assertion loop-annotation statement-contract \
         ghost-code

endif

grammar-check: transf
	./transf -check $(addprefix -builtin ,$(BUILTINS)) $(BNF_FILES)

.PHONY: clean

clean:
	@echo "Cleaning..."
	rm -rf *~ *.aux *.log *.nav *.out *.snm *.toc *.lof *.pp *.bnf \
		*.haux  *.hbbl *.htoc \
                *.cb? *.cm? *.bbl *.blg *.idx *.ind *.ilg *.fls *.fdb_latexmk \
		transf trans.ml pp.ml pp acsl.tex acsl-implementation.tex \
		acslpp.tex acslpp-implementation.tex acsl.pdf \
		acsl-implementation.pdf acslpp.pdf acslpp-implementation.pdf

.PHONY: super-clean
super-clean: clean
	@echo "Removing PDF outputs: $(PDF_OUTPUTS)"
	rm -f $(PDF_OUTPUTS)

# The ACSL document annoted about what is not implemented into Frama-C

acsl-implementation.tex: $(MAIN).tex Makefile
	@rm -f $@
	sed -e '/^% rubber:/s/main.cb/acsl-implementation.cb/g' $^ > $@
	@chmod a-w $@

# The ACSL reference document

acslpp.pdf: $(DEPS_CPP)

acslpp-implementation.pdf: $(DEPS_CPP)

acsl.tex: $(MAIN).tex Makefile
	@rm -f $@
	sed -e '/^% rubber:/s/main.cb/acsl.cb/g' \
	    -e '/^%--.*{PrintImplementationRq}/s/%--//' $^ > $@
	@chmod a-w $@

acslpp.tex: cpp-$(MAIN).tex Makefile
	@rm -f $@
	sed -e '/^% rubber:/s/cpp-main.cb/acslpp.cb/g' \
	    -e '/^%--.*{PrintImplementationRq}/s/%--//' $^ > $@
	@chmod a-w $@

acslpp-implementation.tex: cpp-$(MAIN).tex Makefile
	@rm -f $@
	sed -e '/^% rubber:/s/cpp-main.cb/acslpp-implementation.cb/g' $^ > $@
	@chmod a-w $@

cpp-as-appendix.pdf: cpp-as-appendix.tex $(DEPS) $(DEPS_CPP) $(BNF_DEPS)
	latexmk -f -silent -pdf $<

# Internal to Frama-C
FRAMAC ?= ../../bin/frama-c

HAS_FRAMAC:=$(shell if test -x $(FRAMAC); then echo yes; else echo no; fi)

ifeq ("$(HAS_FRAMAC)","yes")

acsl: acsl-implementation.pdf acsl.pdf acslpp.pdf

all: acsl tutorial full-check

tutorial: tutorial-check acsl-mini-tutorial.pdf

install: acsl-implementation.pdf acsl.pdf acslpp.pdf
	rm -f  ../manuals/acsl-implementation.pdf  ../manuals/acsl.pdf ../manuals/acslpp.pdf
	cp -f acsl-implementation.pdf acsl.pdf acslpp.pdf ../manuals/

tutorial-valid: $(TUTORIAL_EXAMPLES:.c=.proved)
VERSION:
	$(FRAMAC) -version > $@

else
acsl: acsl.pdf acslpp.pdf
tutorial: acsl-mini-tutorial.pdf
all: acsl tutorial

install:
	@echo "install target can only be made within Frama-C sources"
	@exit 2
VERSION:
	@echo "VERSION can only be made within Frama-C sources"
	@exit 2
endif

# Command to produce a diff'ed document. Must be refined to flatten automatically the files
# latexdiff --type=CFONT --append-textcmd="_,sep,alt,newl,is" --append-safecmd="term,nonterm,indexttbase,indextt,indexttbs,keyword,ensuremath" --config "PICTUREENV=(?:picture|latexonly)[\\w\\d*@]*,MATHENV=(?:syntax),MATHREPL=syntax"  full.tex current/full.tex > diff.tex
