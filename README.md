# Description

This directory contains the LaTeX source files for the ACSL reference manual.
ACSL stands for ANSI/ISO C Specification Language and is meant to formally
specify the intended behavior of C programs, in particular through the usage
of function contracts. ACSL is used by the Frama-C platform
(https://frama-c.com/) that gathers a set of C analysis tools.

The ACSL manual is available [here](https://github.com/acsl-language/acsl/wikis/manuals/acsl_1.13.pdf). Older versions are available on [Frama-C's website](https://frama-c.com/acsl.html)

# Requirements

In order to generate a pdf version of the manual, you will need the following:

- a TeX distribution (e.g. TeXlive), including metapost
- latexmk
- ocaml

then, typing `make` should produce the `acsl.pdf` document
