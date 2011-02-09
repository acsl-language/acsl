% --------------------------------------------------------------------------
% ---  LaTeX Class for Frama-C Books                                     ---
% --------------------------------------------------------------------------
\NeedsTeXFormat{LaTeX2e}
\ProvidesPackage{frama-c-book}[2009/02/05 LaTeX Class for Frama-C Books]
% --------------------------------------------------------------------------
% ---  Base Class management                                             ---
% --------------------------------------------------------------------------
\LoadClass[a4paper,11pt,twoside,openright]{report}
\DeclareOption{web}{\PassOptionsToPackage{colorlinks,urlcolor=blue}{hyperref}}
\DeclareOption{paper}{\PassOptionsToPackage{pdfborder=0 0 0}{hyperref}}
\ProcessOptions
\RequirePackage{fullpage}
\RequirePackage{hevea}
\RequirePackage{ifthen}
\RequirePackage[T1]{fontenc}
\RequirePackage[latin1]{inputenc}
\RequirePackage[a4paper,pdftex,pdfstartview=FitH]{hyperref}
\RequirePackage{amssymb}
\RequirePackage{xcolor}
\RequirePackage[pdftex]{graphicx}
\RequirePackage{xspace}
\RequirePackage{makeidx}
\RequirePackage[leftbars]{changebar}
\RequirePackage[english]{babel}
\RequirePackage{fancyhdr}
\RequirePackage{titlesec}
% --------------------------------------------------------------------------
% ---  Page Layout                                                       ---
% --------------------------------------------------------------------------
\setlength{\voffset}{-6mm}
\setlength{\headsep}{8mm}
\setlength{\footskip}{21mm}
\setlength{\textheight}{238mm}
\setlength{\topmargin}{0mm}
\setlength{\textwidth}{155mm}
\setlength{\oddsidemargin}{2mm}
\setlength{\evensidemargin}{-2mm}
\setlength{\changebarsep}{0.5cm}
\setlength{\headheight}{13.6pt}
\def\put@bg(#1,#2)#3{\setlength\unitlength{1cm}%
  \begin{picture}(0,0)(#1,#2)
    \put(0,0){\includegraphics{#3}}
  \end{picture}}
\fancypagestyle{plain}{%
  \fancyfoot{}
  \fancyhead{}
  \fancyhead[LE]{\put@bg(2.4,27.425){frama-c-left.pdf}}
  \fancyhead[LO]{\put@bg(2.7,27.425){frama-c-right.pdf}}
  \fancyhead[CE]{\scriptsize\textsf{\leftmark}}
  \fancyhead[CO]{\scriptsize\textsf{\rightmark}}
  \fancyfoot[C]{\small\textsf{\thepage}}
  \renewcommand{\headrulewidth}{0pt}
  \renewcommand{\footrulewidth}{0pt}
}
\fancypagestyle{blank}{%
  \fancyfoot{}
  \fancyhead{}
  \fancyhead[LE]{\put@bg(2.4,27.425){frama-c-left.pdf}}
  \fancyhead[LO]{\put@bg(2.7,27.425){frama-c-right.pdf}}
}
%% Redefinition of cleardoublepage for empty page being blank
\def\cleardoublepagewith#1{\clearpage\if@twoside \ifodd\c@page\else
\hbox{}
\thispagestyle{#1}
\newpage
\fi\fi}
\def\cleardoublepage{\cleardoublepagewith{blank}}
\pagestyle{plain}

% --------------------------------------------------------------------------
% ---  Cover Page                                                        ---
% --------------------------------------------------------------------------
\newcommand{\coverpage}[1]{%
\thispagestyle{empty}
\setlength\unitlength{1cm}
\begin{picture}(0,0)(3.27,26.75)
\put(0,0){\includegraphics{frama-c-cover.pdf}}
\put(2.0,20.5){\makebox[8cm][l]{\fontfamily{phv}\fontseries{m}\fontsize{24}{2}\selectfont #1}}
\end{picture}
}

% --------------------------------------------------------------------------
% ---  Title Page                                                        ---
% --------------------------------------------------------------------------
\renewenvironment{titlepage}%
{\cleardoublepagewith{empty}\thispagestyle{empty}\begin{center}}%
{\end{center}}
\renewcommand{\title}[2]{
\vspace{20mm}
{\Huge\bfseries #1}

\bigskip

{\LARGE #2}
\vspace{20mm}
}
\renewcommand{\author}[1]{
\vspace{20mm}

{#1}

\medskip
}
% --------------------------------------------------------------------------
% ---  Sectionning                                                       ---
% --------------------------------------------------------------------------
\titleformat{\chapter}[display]{\Huge\raggedleft}%
{\huge\chaptertitlename\,\thechapter}{0.5em}{}
\titleformat{\section}[hang]{\Large\bfseries}{\thesection}{1em}{}%
[\vspace{-14pt}\rule{\textwidth}{0.1pt}\vspace{-8pt}]
\titleformat{\subsubsection}[hang]{\bfseries}{}{}{}%
[\vspace{-8pt}]

% --------------------------------------------------------------------------
% ---  Main Text Style                                                   ---
% --------------------------------------------------------------------------
%\raggedright
\setlength\parindent{0pt}
\setlength\parskip{1ex plus 0.3ex minus 0.2ex}
\newenvironment{warning}[1][Warning:]{\small\paragraph{#1}\itshape}{\vspace{\parskip}}
\def\FramaC{\textsf{Frama-C}\xspace}
% --------------------------------------------------------------------------
% ---  Listings                                                          ---
% --------------------------------------------------------------------------
\RequirePackage{listings}

\lstdefinelanguage{ACSL}{%
  morekeywords={assert,assigns,assumes,axiom,axiomatic,behavior,behaviors,
    boolean,breaks,complete,continues,data,decreases,disjoint,ensures,
    exit_behavior,ghost,global,inductive,integer,invariant,lemma,logic,loop,
    model,predicate,reads,real,requires,returns,sizeof,strong,struct,terminates,type,
    union,variant},
%  otherkeywords={\\at,\\base_addr,\\block_length,\\false,\\fresh,\\from,
%                 \\initialized,\\lambda,\\let,\\match,\\max,\\nothing,\\null,
%                 \\numof,\\old,\\result,\\specified,\\strlen,\\sum,\\true,
%                 \\valid,\\valid_range},
  keywordsprefix={\\},
  alsoletter={\\},
  morecomment=[l]{//}
}

\lstloadlanguages{[ANSI]C,[Objective]Caml,csh,ACSL}
\definecolor{lstbg}{gray}{0.98}
\definecolor{lstfg}{gray}{0.10}
\definecolor{lstrule}{gray}{0.6}
\definecolor{lstnum}{gray}{0.4}
\definecolor{lsttxt}{rgb}{0.3,0.2,0.6}
\definecolor{lstmodule}{rgb}{0.3,0.6,0.2}%{0.6,0.6,0.2}
\definecolor{lstspecial}{rgb}{0.2,0.6,0.0}
\definecolor{lstfile}{gray}{0.85}
\newcommand{\lstbrk}{\mbox{$\color{blue}\scriptstyle\cdots$}}
\def\lp@basic{\ifmmode\normalfont\mathtt\mdseries\scriptsize\else\normalfont\ttfamily\mdseries\scriptsize\fi}
\def\lp@inline{\ifmmode\normalfont\mathtt\scriptstyle\else\normalfont\ttfamily\mdseries\small\fi}
\def\lp@keyword{}
\def\lp@special{\color{lstfg}}
\def\lp@comment{\normalfont\ttfamily\mdseries}
\def\lp@string{\color{lstfg}} \def\lp@ident{}
\def\lp@number{\rmfamily\tiny\color{lstnum}}
\lstdefinestyle{frama-c-style}{%
  basicstyle=\lp@inline,%
  identifierstyle=\lp@ident,%
  commentstyle=\lp@comment,%
  keywordstyle={\ifmmode\mathsf\else\sffamily\fi},%
  keywordstyle=[2]\lp@special,%
  stringstyle=\lp@string,%
  emphstyle=\lp@ident\underbar,%
  showstringspaces=false,%
  mathescape=true,%
  numberstyle=\lp@number,%
  xleftmargin=6ex,xrightmargin=2ex,%
  framexleftmargin=1ex,%
  frame=l,%
  framerule=1pt,%
  rulecolor=\color{lstrule},%
  backgroundcolor=\color{lstbg},%
  moredelim={*[s]{/*@}{*/}},%
  moredelim={*[l]{//@}},
  morecomment={[is]{//NOPP-BEGIN}{NOPP-END}},
  mathescape=true,
  escapechar=`
% breaklines is broken when using a inline and background
%  breaklines,prebreak={\lstbrk},postbreak={\lstbrk},breakindent=5ex %
}

\lstdefinestyle{c}%
{language={[ANSI]C},alsolanguage=ACSL,style=frama-c-style}
\lstdefinestyle{c-basic}%
{language={[ANSI]C},alsolanguage=ACSL,style=frama-c-style,basicstyle=\lp@basic}


% --- C/ACSL Stuff ---------------------------------------------------------
% Make 'c' the default style
\lstset{style=c}

\newcommand{\listinginput}[3][1]%
{\lstinputlisting[style=c-basic,numbers=left,stepnumber=#1,firstnumber=#2]{#3}}

\lstnewenvironment{listing}[2][1]%
{\lstset{style=c-basic,numbers=left,stepnumber=#1,firstnumber=#2}}{}

\lstnewenvironment{listing-nonumber}%
{\lstset{style=c,numbers=none,basicstyle=\lp@basic}}{}

% --- Verbatim Stuff -------------------------------------------------------
\lstdefinelanguage{Shell}[]{csh}%
{identifierstyle=\lp@basic,mathescape=false,backgroundcolor=,literate={\\\$}{\$}1}
\lstnewenvironment{shell}[1][]{\lstset{language=Shell,basicstyle=\lp@basic,#1}}{}

% ---- Stdout Stuff --------------------------------------------------------
\lstdefinelanguage{Logs}[]{csh}%
{identifierstyle=\lp@basic,backgroundcolor=}
\lstnewenvironment{logs}[1][]{\lstset{language=Logs,basicstyle=\lp@basic,#1}}{}
\newcommand{\logsinput}[1]%
{\lstinputlisting[language=Logs,basicstyle=\lp@basic]{#1}}

% --------------------------------------------------------------------------
% ---  Developer Code Stuff                                              ---
% --------------------------------------------------------------------------

\newcommand{\listingname}[1]{\colorbox{lstfile}{\footnotesize\sffamily File \bfseries #1}\vspace{-4pt}}

% --- Style ----------------------------------------------------------------
\lstdefinestyle{framac-code-style}{%
basicstyle=\lp@inline,%
numberstyle=\lp@number,%
keywordstyle=[1]\sffamily\color{lstmodule},%
keywordstyle=[2]\sffamily\color{lstspecial},%
keywordstyle=[3]\sffamily\bfseries,%
identifierstyle=\rmfamily,%
stringstyle=\ttfamily\color{lstfg},%
commentstyle=\rmfamily\bfseries\color{lsttxt},%
}
\lstdefinestyle{framac-shell-style}{%
mathescape=false,%
basicstyle=\lp@basic,%
numberstyle=\lp@number,%
keywordstyle=\sffamily\bfseries,%
keywordstyle=[1]\sffamily\color{lstmodule},%
keywordstyle=[2]\sffamily\color{lstspecial},%
keywordstyle=[3]\sffamily\bfseries,%
identifierstyle=\ttfamily,%
stringstyle=\ttfamily\color{lstfg},%
commentstyle=\rmfamily\bfseries\color{lsttxt},%
literate={\\\$}{\$}1,%
}
% --- Configure ------------------------------------------------------------
\lstdefinelanguage{Configure}[]{csh}{%
style=framac-shell-style,%
morekeywords={fi},%
}
\lstnewenvironment{configurecode}[1][]%
{\lstset{language=Configure,#1}}{}
\newcommand{\configureinput}[1]{\lstinputlisting[language=Configure]{#1}}
% --- Makefile  ------------------------------------------------------------
\lstdefinelanguage{Makefile}[]{make}{%
style=framac-shell-style,%
morekeywords={include},%
}
\lstnewenvironment{makefilecode}[1][]%
{\lstset{language=Makefile,#1}}{}
\newcommand{\makefileinput}[1]{\lstinputlisting[language=Makefile]{#1}}
% --- C- for Developer  ----------------------------------------------------
\lstdefinestyle{framac-code}%
  {language={[ANSI]C},alsolanguage=ACSL,style=framac-code-style,basicstyle=\lp@basic}
\lstnewenvironment{ccode}[1][]%
{\lstset{language={[ANSI]C},alsolanguage=ACSL,style=framac-code-style,basicstyle=\lp@basic,#1}}{}
\newcommand{\cinput}[1]%
{\lstinputlisting[language={[ANSI]C},alsolanguage=ACSL,style=framac-code-style,basicstyle=\lp@basic]{#1}}
\newcommand{\cinline}[1]%
{\lstinline[style=framac-code]{#1}}
% --- Ocaml ----------------------------------------------------------------
\lstdefinelanguage{Ocaml}[Objective]{Caml}{%
style=framac-code-style,%
deletekeywords={when,module,struct,sig,begin,end},%
morekeywords=[2]{failwith,raise,when},%
morekeywords=[3]{module,struct,sig,begin,end},%
literate=%
{~}{${\scriptstyle\thicksim}$}1%
{<}{$<$}1%
{>}{$>$}1%
{->}{$\rightarrow$}1%
{<-}{$\leftarrow$}1%
{:=}{$\leftarrow$}1%
{<=}{$\leq$}1%
{>=}{$\geq$}1%
{==}{$\equiv$}1%
{!=}{$\not\equiv$}1%
{<>}{$\neq$}1%
{'a}{$\alpha$}1%
{'b}{$\beta$}1%
{'c}{$\gamma$}1%
{µ}{`{}}1%
}

\lstdefinestyle{ocaml-basic}%
{language=Ocaml,basicstyle=\lp@basic}
\newcommand{\ocamlinput}[2][]{\lstinputlisting[style=ocaml-basic,#1]{#2}}
\lstnewenvironment{ocamlcode}[1][]{\lstset{style=ocaml-basic,#1}}{}
% --------------------------------------------------------------------------
\lstdefinelanguage{Why}{%
  morekeywords={
    type, logic, axiom, predicate, goal,
    forall, let, in,
  },
  morecomment=[s]{(*}{*)},
  alsoletter={_},
  literate=%
  {->}{$\Rightarrow$}1%
  {forall}{$\forall$}1%
  {not}{$\neg$}1%
  {<>}{$\neq$}1%
  {...}{$\dots$}1%
  %{_}{\_}1%
  %{_}{{\rule[0pt]{1ex}{.2pt}}}1%
  }

\lstdefinestyle{why-style}{%
language=Why,%
style=framac-code-style,%
basicstyle=\lp@basic,%
}

\lstnewenvironment{whycode}[1][]{\lstset{style=why-style,#1}}{}
\newcommand{\whyinput}[1]%
{\lstinputlisting[style=why-style]{#1}}
\newcommand{\whyinline}[1]%
{\lstinline[style=why-style]{#1}}

% --------------------------------------------------------------------------
% ---  End.                                                              ---
% --------------------------------------------------------------------------
