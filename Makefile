default: acsl.pdf

MAIN=main

PDF_OUTPUTS_CPP=acslpp-implementation.pdf acslpp.pdf
PDF_OUTPUTS_C=acsl-implementation.pdf acsl.pdf
PDF_OUTPUTS=$(PDF_OUTPUTS_C) $(PDF_OUTPUTS_CPP)

BNF_FILES=term.tex predicate.tex binders.tex fn_behavior.tex \
          oldandresult.tex at.tex loc.tex assertions.tex loops.tex  \
          assertions.tex loops.tex allocation.tex			\
          generalinvariants.tex st_contracts.tex ghost.tex model.tex	\
          logic.tex inductive.tex logicdecl.tex logictypedecl.tex	\
          higherorder.tex logiclabels.tex logicreads.tex memory.tex	\
          initialized.tex data_invariants.tex volatile-gram.tex		\
          exitbehavior.tex dependencies.tex welltyped.tex		\
          list-gram.tex c-type-name.tex cpp-functional-gram.tex		\
          cpp-exceptionbehavior.tex cpp-default-values-syntax.tex	\
          cpp-class-invariants-fig.tex cpp-this.tex cpp-gram-pure.tex   \
          cpp-casts.tex attribute.tex

BNF_DEPS=$(BNF_FILES:.tex=.bnf)

DEPS= main.tex version.tex changes.tex common.tex speclang_modern.tex	\
	macros_modern.tex intro_modern.tex libraries_modern.tex		\
	compjml_modern.tex div_lemma.c assigns.c invariants.c		\
	example-lt-modern.tex biblio.bib malloc_free_fn.c		\
	malloc-free2-fn.c loop-frees.c isqrt.c sizeof.c incrstar.c	\
	parsing_annot_modern.tex integer-cast-modern.tex max.c		\
	max_index.c cond_assigns.c bsearch.c bsearch2.c			\
	assigns_array.c assigns_list.c sum.c listdecl.c listdef.c	\
	listlengthdef.c import.c listmodule.c strcpyspec.c dowhile.c	\
	num_of_pos.c nb_occ.c nb_occ_reads.c builtins.tex permut.c	\
	permut_reads.c acsl_allocator.c preprocessing.tex		\
	gen_spec_with_model.c gen_code.c out_char.c ghostpointer.c	\
	ghostcfg.c flag.c lexico.c footprint.c loopvariantnegative.c	\
	fact.c mutualrec.c abrupt_termination.c				\
	advancedloopinvariants.c inductiveloopinvariants_modern.tex	\
	$(BNF_DEPS) cfg.mps volatile.c euclide.c initialized.c		\
	dangling.c sum2.c modifier.c gen_spec_with_ghost.c		\
	terminates_list.c glob_var_masked.c glob_var_masked_sol.c	\
	intlists.c sign.c signdef.c oldat.c mean.c isgcd.c exit.c	\
	mayexit.c loop_current.c welltyped.c list-observer.c		\
	c-grammar.tex Makefile

DEPS_CPP=cpp-abstraction.tex cpp-attributes.tex cpp-auto.tex		\
    cpp-class-contracts.tex cpp-class-invariants.tex			\
    cpp-default-values.tex cpp-defensive.tex cpp-enum.tex		\
    cpp-exceptions.tex cpp-foreword.tex cpp-forrange.tex		\
    cpp-functional-design.tex cpp-functional-examples.tex		\
    cpp-functional.tex cpp-namespaces.tex cpp-templates.tex		\
    overload_contract.cpp ffunctorB.cpp cpp-types.tex cpp-type.tex	\
    cpp-visibility.tex cpp-changes.tex fexample1.cpp fexampleA.cpp	\
    fexampleA.logic fexampleA.smt2 fexampleB.cpp fexampleB.logic	\
    fexampleB.smt2 fexampleC.cpp fexampleC.logic fexampleD1.logic	\
    fexampleD2.logic fexampleD.cpp fexampleD.logic

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

ifeq ("$(DRAFT)","yes")
  DRAFT_OPT="-usepretex=\PassOptionsToPackage{status=draft}{fixme}"
else
  DRAFT_OPT=
endif

$(PDF_OUTPUTS): %.pdf: main.tex $(DEPS) $(BNF_DEPS)
	latexmk -silent -pdf -jobname=$* $(DRAFT_OPT) $<

$(PDF_OUTPUTS_CPP): $(DEPS_CPP)

acsl-implementation.pdf: fc_version.tex

acslpp-implementation.pdf: fc_version.tex fclang_version.tex

%.pdf: %.tex $(DEPS) $(BNF_DEPS)
	latexmk -silent -pdf $<

SHORT_VERSION ?= ../../VERSION
HAS_SHORT_VERSION:=$(shell if test -f $(SHORT_VERSION); then echo yes; else echo no; fi)

FCLANG_VERSION_FILE?=../../src/plugins/frama-clang/MAKEFILE
HAS_FCLANG:=$(shell if test -f $(FCLANG_VERSION_FILE); then echo yes; else echo no; fi)

ifneq ("$(HAS_SHORT_VERSION)","yes")

fc_version.tex: Makefile
	@echo "Cannot get the Frama-C version out of frama-c doc directory"
	@echo "Generating a joker version number for implementation"
	@rm -f $@
	@printf '\\newcommand{\\fcversion}{XX.X}\n' > $@

else

fc_version.tex: Makefile $(SHORT_VERSION)
	@rm -f $@
	@printf '\\newcommand{\\fcversion}{$(shell cat $(SHORT_VERSION))}\n' > $@

endif

ifneq ("$(HAS_FCLANG)","yes")
fclang_version.tex: Makefile
	@echo "Cannot find $(FCLANG_VERSION_FILE)."
	@echo "Consider setting FCLANG_VERSION_FILE to an appropriate file"
	@rm -f $@
	@printf '\\newcommand{\\fclangversion}{YY.Y}\n' > $@
else
FCLANG_VERSION:=$(shell grep -e FCLANG_VERSION= $(FCLANG_VERSION_FILE) | \
                         sed -e 's/[^=]*=\(.*\)/\1/')

fclang_version.tex: Makefile $(FCLANG_VERSION_FILE)
	@rm -f $@
	@printf '\\newcommand{\\fclangversion}{$(FCLANG_VERSION)}' > $@
endif

pp: pp.ml
	ocamlopt -o $@ str.cmxa $^

transf: transf.cmo transfmain.cmo
	ocamlc -o $@ $^

%.cmo: %.ml
	ocamlc -c $<

%.proved:%.c acsl-mini-tutorial.tex
	$(FRAMAC) -wp $<
	touch $@

transfmain.cmo: transf.cmo

# Internal to Frama-C
FRAMAC ?= ../../bin/frama-c
FRAMAC_MANUALS = $(dir $(FRAMAC))/../doc/manuals

HAS_FRAMAC:=$(shell if test -x $(FRAMAC); then echo yes; else echo no; fi)
HAS_FRAMAC_MANUALS:=$(shell if test -d $(FRAMAC_MANUALS); then echo yes; else echo no; fi)

.PHONY: full-check check tutorial-check grammar-check
full-check: check tutorial-check grammar-check

ifneq ("$(HAS_FRAMAC)","yes")

.PHONY: cannot-check
cannot-check:
	@echo "check targets can only be made within Frama-C binary"
	@exit 2

tutorial-check: cannot-check
check: cannot-check

else
HAS_FCLANG=$(shell if $(FRAMAC) -plugins | grep -q "Frama_Clang"; \
                   then echo yes; else echo no; fi)

GOOD=abrupt_termination.c advancedloopinvariants.c assert-tut.c		\
assigns_array.c assigns.c assigns_list.c bsearch.c bsearch2.c		\
cond_assigns.c div_lemma.c dowhile.c euclide.c exit.c extremum-tut.c	\
extremum2-tut.c fact.c flag.c footprint.c 				\
glob_var_masked.c glob_var_masked_sol.c global_invariant-tut.c		\
incrstar.c initialized.c intlists.c isgcd.c isqrt.c listdecl.c		\
listdef.c loopvariantnegative.c loop-frees.c loop_current.c             \
malloc_free_fn.c malloc-free2-fn.c max-tut.c max.c max_index.c		\
max_list-tut.c max_ptr-tut.c max_ptr2-tut.c max_ptr_bhv-tut.c		\
max_ptr_false-tut.c max_seq-tut.c max_seq2-tut.c			\
max_seq_assigns-tut.c max_seq_ghost-tut.c max_seq_inv-tut.c		\
max_seq_old-tut.c max_seq_old2-tut.c mayexit.c mean.c minitutorial.c	\
mutualrec.c nb_occ.c nb_occ_reads.c non_terminating-tut.c		\
non_terminating2-tut.c num_of_pos.c oldat.c permut.c permut_reads.c	\
redeclaredat.c sizeof.c sign.c signdef.c sort.c specified.c		\
sqsum-tut.c sqsum2-tut.c strcpyspec.c sum.c swap-tut.c			\
terminates_list.c type_invariant-tut.c volatile.c dangling.c		\
welltyped.c list-observer.c

BAD=acsl_allocator.c arrayslice.c gen_code.c gen_spec_with_ghost.c	\
gen_spec_with_model.c ghostcfg.c import.c invariants.c			\
lexico.c listlengthdef.c listmodule.c                                   \
modifier.c out_char.c sum2.c ghost_qualifier.c ghostpointer.c

ifeq ("$(HAS_FCLANG)","yes")
CHECK_FILES=*.c *.cpp
else
CHECK_FILES=*.c
endif

C_FILES:=$(wildcard *.c)
CPP_FILES:=$(wildcard *.cpp)

C_CHECK:=$(C_FILES:.c=.check)
CPP_CHECK:=$(CPP_FILES:.cpp=.check)

check-c-files: $(C_CHECK)
check-cpp-files: $(CPP_CHECK)

%.check: %.c
	gcc -std=c99 -c -Wall -Werror $(WFLAGS) $^

%.check: %.cpp
	g++ -std=c++11 -c -Wall -Werror $(WFLAGS) $^

# some examples are intended to trigger gcc warnings
dangling.check: WFLAGS:=-Wno-return-local-addr
redeclaredat.check: WFLAGS:=-Wno-unused-label

pure.check: WFLAGS:=-Wno-unused-label

check: acsl-mini-tutorial.tex
	$(MAKE) -k check-c-files
	$(MAKE) -k check-cpp-files
	@good=0; \
        bad=0; \
        failed=0; \
        passed=0; \
	failed_list=""; \
        passed_list=""; \
        for f in $(CHECK_FILES); do \
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
endif

BUILTINS=real integer string character id

grammar-check: transf
	./transf -check $(addprefix -builtin ,$(BUILTINS)) $(BNF_FILES)

.PHONY: clean

clean-tools:
	@echo "Cleaning generated tools..."
	rm -f transf transf.ml pp.ml pp *.cm?

clean: clean-tools
	@echo "Cleaning..."
	rm -rf *~ *.aux *.log *.nav *.out *.snm *.toc *.lof *.pp *.bnf \
		*.haux  *.hbbl *.htoc \
                *.cb? *.cm? *.bbl *.blg *.idx *.ind *.ilg *.fls *.fdb_latexmk \
		transf trans.ml pp.ml pp

.PHONY: super-clean
super-clean: clean
	@echo "Removing PDF outputs: $(PDF_OUTPUTS)"
	rm -f $(PDF_OUTPUTS)

acsl: $(PDF_OUTPUTS)

# Internal to Frama-C
FRAMAC ?= ../../bin/frama-c

HAS_FRAMAC:=$(shell if test -x $(FRAMAC); then echo yes; else echo no; fi)

ifeq ("$(HAS_FRAMAC)","yes")

all: acsl tutorial full-check

tutorial: tutorial-check acsl-mini-tutorial.pdf

tutorial-valid: $(TUTORIAL_EXAMPLES:.c=.proved)
VERSION:
	$(FRAMAC) -version > $@

else
tutorial: acsl-mini-tutorial.pdf
all: acsl tutorial

VERSION:
	@echo "VERSION can only be made within Frama-C binary"
	@exit 2
endif

ifeq ("$(HAS_FRAMAC_MANUALS)","yes")
install: acsl-implementation.pdf acsl.pdf
	rm -f  $(FRAMAC_MANUALS)/acsl-implementation.pdf  $(FRAMAC_MANUALS)/acsl.pdf
	cp -f acsl-implementation.pdf acsl.pdf $(FRAMAC_MANUALS)/
else
install:
	@echo "install target can only be made within directory Frama-C manuals"
	@exit 2
endif

# Command to produce a diff'ed document. Must be refined to flatten automatically the files
# latexdiff --type=CFONT --append-textcmd="_,sep,alt,newl,is" --append-safecmd="term,nonterm,indexttbase,indextt,indexttbs,keyword,ensuremath" --config "PICTUREENV=(?:picture|latexonly)[\\w\\d*@]*,MATHENV=(?:syntax),MATHREPL=syntax"  full.tex current/full.tex > diff.tex
