# Description

This directory contains the LaTeX source files for the ACSL and ACSL++ reference manuals.
ACSL stands for ANSI/ISO C Specification Language and is meant to formally
specify the intended behavior of C programs, in particular through the usage
of function contracts. ACSL++ is the corresponding language for C++.
ACSL and ACSL++ are used by the Frama-C platform
(https://frama-c.com/) that unifies a set of C/C++ analysis tools.

Releases of the ACSL/ACSL++ manual are available [here](https://github.com/acsl-language/acsl/releases). Older versions are also available on [Frama-C's website](https://frama-c.com/acsl.html)

# Requirements

In order to generate a pdf version of the manual, you will need the following:

- a TeX distribution (e.g. TeXlive), including metapost
- latexmk
- ocaml

then, typing `make acsl.pdf` or `make acslpp.pdf` should produce
the `acsl.pdf` and acslpp.pdf documents, respectively.

It is also possible, for both documents, to activate a draft mode that will
show some comments about possible extensions and enhancements. To do that,
use `make DRAFT=yes acsl.pdf` or `make DRAFT=yes acslpp.pdf`

# Frama-C's implementation notes

If this directory is located inside the `doc` directory of a Frama-C
distribution, it is possible to also generate implementation notes manuals
(for both ACSL and ACSL++) indicating the level of support of each feature
inside the tool, and perform various consistency checks. Use the `make all`
command for that.
