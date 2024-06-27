\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{frama-c-book}
\LoadClass[a4paper]{report}

\RequirePackage{kvoptions}
\SetupKeyvalOptions{
  family=framacbook,
  prefix=framacbook@,
}
\DeclareStringOption[english]{lang}
\ProcessKeyvalOptions*

\PassOptionsToPackage{\framacbook@lang}{babel}

\RequirePackage{babel}

\RequirePackage[
  left=.125\paperwidth,
  right=.125\paperwidth,
  top=.125\paperheight,
  bottom=.125\paperheight
]{geometry}
\RequirePackage[dvipsnames,table]{xcolor}
\RequirePackage{graphicx}
\RequirePackage{xspace}
\RequirePackage{anyfontsize}
\RequirePackage{titletoc}
\RequirePackage{titlesec}
\RequirePackage[shortlabels]{enumitem}
\RequirePackage{fancyhdr}
\RequirePackage{lmodern}
\RequirePackage{microtype}
\RequirePackage{etoolbox}

\RequirePackage{tikz}
\usetikzlibrary{fadings}

% Do I keep it there:

\RequirePackage[T1]{fontenc}
\RequirePackage[utf8]{inputenc}
\RequirePackage{amssymb}
\RequirePackage{comment}


\definecolor{frama-c-orange}{HTML}{F36521}
\definecolor{frama-c-dark-orange}{HTML}{D04604}
\definecolor{frama-c-dark-red}{HTML}{D00404}
\definecolor{frama-c-bronze}{HTML}{F39D21}
\definecolor{frama-c-green}{HTML}{16A371}
\definecolor{frama-c-dark-green}{HTML}{0E6647}

\RequirePackage[
  pdftex,pdfstartview=FitH,
  bookmarks=true,
  hyperindex=true,
  bookmarksopen=true,
  bookmarksnumbered=true,
  colorlinks=true,
  allcolors={frama-c-dark-orange}
]{hyperref}

% --------------------------------------------------------------------------
% CEA commands
% --------------------------------------------------------------------------

\newcommand{\cealist}{CEA-List}
\newcommand
  {\fcaffiliationen}
  {\cealist, Université Paris-Saclay\\ Software Safety and Security Lab\xspace}
\newcommand
  {\fcaffiliationfr}
  {\cealist, Université Paris-Saclay\\ Laboratoire de Sûreté et Sécurité des Logiciels\xspace}

\newcommand{\cealogo}{logos/cea_tech_list.png}

% --------------------------------------------------------------------------
% LICENSE commands
% --------------------------------------------------------------------------

\def\@licence{}
\def\@licencelogo{}
\def\@licencelink{}
\newcommand{\licence}[3]{
  \def\@licence{#1}
  \def\@licencelogo{#2}
  \def\@licencelink{#3}
}
\newcommand{\cclicence}[1]{
  \licence
    {Creative Commons \uppercase{#1}}
    {logos/#1.png}
    {\url{https://creativecommons.org/licenses/#1/4.0/}}
}

% --------------------------------------------------------------------------
% Copyright commands
% --------------------------------------------------------------------------

\def\@copyrightfrom{}
\newcommand{\copyrightstarts}[1]{
  \def\@copyrightfrom{#1}
}

\newcommand{\addcopyrightowner}[1]{
  \listadd{\@copyrightowner}{#1}
}
\addcopyrightowner{\cealist} % add it by default

\newcommand{\insertcopyrightowners}{{
  \def\listsep{\def\listsep{, }}%
  \renewcommand{\do}[1]{\listsep##1}%
  \dolistloop\@copyrightowner
}}

\newcommand{\insertcopyright}{
  \textcopyright\xspace \@copyrightfrom-\the\year{} \insertcopyrightowners
}

% --------------------------------------------------------------------------
% Logos
% --------------------------------------------------------------------------

\def\@logos{}
\newcommand{\addlogo}[1]{
  \listadd{\@logos}{#1}
}
\addlogo{\cealogo} % add it by default

\newcommand{\insertlogos}{{
  \def\listsep{\def\listsep{\hspace{2em}}}%
  \renewcommand{\do}[1]{\listsep\includegraphics[height=7em]{##1}}%
  \dolistloop\@logos
}}

% --------------------------------------------------------------------------
% Subtitle
% --------------------------------------------------------------------------

\def\@subtitle{}

\newcommand{\subtitle}[1]{
  \def\@subtitle{#1}
}

% --------------------------------------------------------------------------
% Frama-C commands
% --------------------------------------------------------------------------

\def\@fcversion{}
\newcommand{\fcversion}[1]{
  \subtitle{For Frama-C #1}
}

\def\fchrulefill{\leavevmode\leaders\hrule height 1.25pt\hfill\kern\z@}


% --------------------------------------------------------------------------
% Title page
% --------------------------------------------------------------------------

\renewcommand{\maketitle}{%
  \newgeometry{top=1cm, bottom=1cm, right=1cm,left=1cm}
  \thispagestyle{empty}
  \noindent\includegraphics{logos/frama-c.png}

  \vspace{12em}
  \begin{center}
    \textbf{\Huge\@title}

    \medskip
    \ifx\@subtitle\empty\else{
      \Large \@subtitle
    }\fi
  \end{center}

  \vspace{-1em}
  {\noindent\color{frama-c-orange}\fchrulefill}

  \begin{center}
    \begin{minipage}{.8\textwidth}
      \centering
      \large\@author
    \end{minipage}
  \end{center}

  \bigskip

  \begin{center}
    \insertlogos
  \end{center}

  \vfill

  \noindent
  \ifx\@licencelogo\empty
  \else{
  \begin{minipage}{.14\textwidth}
    \includegraphics[height=25pt]{\@licencelogo}
  \end{minipage}
  \hfill
  }
  \fi
  \begin{minipage}{.84\textwidth}
    \vspace{.2em}
    \ifx\@licence\empty
    \else{\large Work licensed under \@licence\xspace licence}\fi\\
    \ifx\@licencelink\empty
    \else{\large\@licencelink}\fi
  \end{minipage}
  \medskip

  \noindent\insertcopyright

  \restoregeometry%

  \cleardoublepage
}

% --------------------------------------------------------------------------
% Table of contents
% --------------------------------------------------------------------------

\titlecontents{chapter}
  [0em]
  {\bigskip}
  {\makebox[2em][l]{\thecontentslabel}\bfseries}
  {\hspace*{2em}\bfseries}
  {\space\hfill\makebox[1.5em]{\contentspage}}[]

\titlecontents{section}
  [2em]
  {\medskip}
  {\makebox[3em][l]{\thecontentslabel}}
  {\hspace*{3em}}
  {\titlerule*[1pc]{.}\makebox[1.5em]{\contentspage}}[]

\titlecontents{subsection}
  [5em]
  {\smallskip}
  {\makebox[4.5em][l]{\thecontentslabel}}
  {\hspace*{4.5em}}
  {\titlerule*[1pc]{.}\makebox[1.5em]{\contentspage}}[]

% --------------------------------------------------------------------------
% Acknoledgements
% --------------------------------------------------------------------------

\def\@people{}
\newcommand{\acknowledge}[1]{
  \listadd{\@people}{#1}
}

\newcommand{\commaorandlist}[1]{%
  \count255=0
  \def\do##1{\advance\count255 1 \chardef\finalitem=\count255 }%
  \dolistloop{#1}%
  \count255=0
  \def\do##1{\advance\count255 1
    \ifnum\count255=\finalitem
      \space and\space
    \else
      \ifnum\count255=1\else,\space\fi
    \fi##1}
  \dolistloop{#1}}

\newcommand{\insertpeople}{{
  \ifx\@people\empty\else
  {We gratefully thank all the people who contributed to this document: \commaorandlist\@people.}
  \fi
}}

% \acknowledgeprogram{<flag image file>}{<text inside box>}
\newcommand{\acknowledgeprogram}[2]{
  \noindent\fbox{%
    \parbox{\dimexpr\linewidth-2\fboxsep-2\fboxrule}{%
      \begin{minipage}{1.2cm}%
        \includegraphics[width=\textwidth]{#1}%
      \end{minipage}%
      \hfill%
      \begin{minipage}{0.9\textwidth}%
        This project has received funding from #2.%
      \end{minipage}%
    }%
  }%
}

\newcommand{\acknowledgeANR}[1]{
  \acknowledgeprogram{anr-logo.png}{#1}
}

\newcommand{\acknowledgeEU}[1]{
  \acknowledgeprogram{eu-flag.jpg}{#1}
}

% --------------------------------------------------------------------------
% Header
% --------------------------------------------------------------------------

\pagestyle{fancy}
\fancyhf{}
\fancyhead[L]{\vspace{1.25em}\raggedleft\rightmark\vspace{-1.25em}}
\fancyfoot[C]{\thepage}
\renewcommand{\headrulewidth}{0pt}
\setlength{\headheight}{24pt}

% --------------------------------------------------------------------------
% Chapters
% --------------------------------------------------------------------------

\titleformat{\chapter}[display]
  {\sc\huge}
  {\filleft\fontsize{50}{0}\selectfont\thechapter}
  {-1.1em}
  {\filright}
  [\normalsize\vspace{-.5em}\color{frama-c-orange}\fchrulefill]

\titleformat{\section}[hang]
  {\Large\bfseries}
  {\thesection}
  {1em}
  {}
  [\vspace{-10pt}\rule{\textwidth}{0.1pt}\nopagebreak\vspace{-8pt}]

\titlespacing*{\section}{0pt}{20pt}{20pt}

% --------------------------------------------------------------------------
% Itemize style
% --------------------------------------------------------------------------

\renewcommand\labelitemi{--}
\setitemize{noitemsep,topsep=5pt,parsep=0pt,partopsep=0pt}
\setenumerate{noitemsep,topsep=5pt,parsep=0pt,partopsep=0pt}

% --------------------------------------------------------------------------
% Footnote style
% --------------------------------------------------------------------------

\renewcommand\footnoterule{%
  \kern-3\p@%
  {\color{frama-c-orange}\hrule\@width\columnwidth}%
  \kern2.6\p@%
}

\renewcommand{\@makefntext}[1]{
 \setlength{\parindent}{0pt}
 \begin{list}{}{\setlength{\labelwidth}{1.5em}
 \setlength{\leftmargin}{\labelwidth}
 \setlength{\labelsep}{3pt}
 \setlength{\itemsep}{0pt}
 \setlength{\parsep}{0pt}
 \setlength{\topsep}{3pt}
 \footnotesize}
 \item[\@makefnmark\hfil]#1
 \end{list}
}

% --------------------------------------------------------------------------
% Warning & information style
% --------------------------------------------------------------------------

\newsavebox{\fcsavebox}
\newenvironment{colbox}[1]{%
  \newcommand\colboxcolor{#1}%
  \begin{lrbox}{\fcsavebox}%
  \begin{minipage}{\dimexpr\linewidth-2\fboxsep\relax}
  \itshape
}{%
  \end{minipage}\end{lrbox}%
  \begin{center}
    \colorbox{\colboxcolor}{\usebox{\fcsavebox}}
  \end{center}
}

\newenvironment{important}{\begin{colbox}{frama-c-dark-orange!30}}{\end{colbox}}
\newenvironment{information}{\begin{colbox}{frama-c-green!30}}{\end{colbox}}

% --------------------------------------------------------------------------
% Code
% --------------------------------------------------------------------------

\RequirePackage{scrhack} % avoids warning about \float@addtolists related to lstlisting
\RequirePackage{listings}
\RequirePackage{caption}
\RequirePackage{accsupp}

\newcommand{\noncopynumber}[1]{%
  \BeginAccSupp{method=escape,ActualText={}}%
  #1%
  \EndAccSupp{}%
}

\renewcommand{\ttdefault}{pcr} % so that keywords can be bold

% CAPTION

\DeclareCaptionFormat{listing}{
  \raggedright\textbf{#1 #2} #3
  \vspace{-2mm}
  {\color{gray}\rule{\textwidth}{0.1pt}}
}
\DeclareCaptionLabelSeparator{listing}{--}
\captionsetup[lstlisting]{format=listing,labelsep=listing}

% Basic style
% --------------------------------------------------------------------------

\definecolor{lstnum}{gray}{0.3}
\definecolor{lsttxt}{rgb}{0.3,0.2,0.6}
\definecolor{lstmodule}{rgb}{0.3,0.6,0.2}
\definecolor{lstspecial}{rgb}{0.2,0.6,0.0}
\definecolor{lstfile}{gray}{0.85}
\definecolor{lstcomments}{rgb}{0.35,0.35,0.35}

\newcommand{\lstbrk}{\mbox{$\color{blue}\scriptstyle\cdots$}}

\def\lp@basic{\ifmmode\normalfont\mathtt\mdseries\small\else\normalfont\ttfamily\mdseries\small\fi}
\def\lp@inline{\ifmmode\normalfont\mathtt\scriptstyle\else\normalfont\ttfamily\mdseries\normalsize\fi}
\def\lp@keyword{}
\def\lp@special{\color{frama-c-dark-orange}}
\def\lp@comment{\normalfont\ttfamily\mdseries\color{lstcomments}}
\def\lp@string{\color{frama-c-dark-green}}
\def\lp@ident{}
\def\lp@number{\rmfamily\tiny\color{lstnum}\noncopynumber}

\lstdefinestyle{frama-c-basic-style}{%
  captionpos=b,%
  columns=flexible,%
  basicstyle=\lp@inline,%
  identifierstyle=\lp@ident,%
  commentstyle=\lp@comment,%
  keywordstyle={\bfseries\ifmmode\mathsf\else\ttfamily\fi\color{blue}},%
  keywordstyle=[2]\bfseries\lp@special,%
  stringstyle=\lp@string,%
  emphstyle=\lp@ident\underbar,%
  showstringspaces=false,%
  numberstyle=\lp@number,%
  xleftmargin=1.82em,%
  framexleftmargin=1ex,%
  frame=l,%
  framerule=1pt,%
  rulecolor=\color{frama-c-orange!60},%
  backgroundcolor=\color{frama-c-bronze!10},%
  literate={\ }{\ }1,
  % ^~~~~  Without this, spaces starting a line does not have the right size ...
}

\lstdefinestyle{frama-c-style}{%
  style=frama-c-basic-style,%
  moredelim={*[s]{/*@}{*/}},%
  moredelim={*[l]{//@}},%
  morecomment={[il]{//NOPP-LINE}},% invisible comment until end of line
  morecomment={[is]{//NOPP-BEGIN}{NOPP-END\^^M}},% no space after NOPP-END
  mathescape=true,
}

% Code styles
% --------------------------------------------------------------------------

\lstdefinestyle{frama-c-shell-style}{%
  mathescape=false,%
  basicstyle=\lp@basic,%
  keywordstyle=\sffamily\bfseries,%
  keywordstyle=[1]\sffamily\color{lstmodule},%
  keywordstyle=[2]\sffamily\color{lstspecial},%
  keywordstyle=[3]\sffamily\bfseries,%
  identifierstyle=\ttfamily,%
  stringstyle=\ttfamily\color{frama-c-orange},%
  commentstyle=\rmfamily\bfseries\color{lsttxt},%
  literate={\\\$}{\$}1%
  {€}{\textbackslash}1%
,%
}

% ACSL + C
% --------------------------------------------------------------------------

\lstdefinelanguage{ACSL}{%
	escapechar={},
	literate=,
	breaklines=false,
	classoffset=1,
	morekeywords={admit,allocates,assert,assigns,assumes,axiom,axiomatic,behavior,
	  behaviors,boolean,breaks,calls,check,complete,continues,data,decreases,disjoint,
    ensures,exits,frees,ghost,global,import,inductive,integer,invariant,lemma,
    logic,loop,model,module,predicate,reads,real,requires,sizeof,strong,struct,
    terminates,returns,type,union,variant,
    dynamic_split,merge,pragma,slevel,split,taints,taint,unroll,widen_hints,
    \\tainted,
    Here,LoopCurrent,LoopEntry,Pre,Post,Old,
    \\Cons,\\Down,\\NearestAway,\\NearestEven,\\Nil,\\ToZero,\\Up,
    \\at,\\allocable,\\allocation,\\automatic,\\base_addr,\\block_length,\\dangling,
    \\dynamic,\\exists,\\exit_status,\\false,\\forall,\\freeable,\\fresh,\\from,
    \\in,\\initialized,\\lambda,\\let,\\list,\\match,\\nothing,\\null,\\numof,
    \\object_pointer,\\offset,\\old,\\register,\\result,\\separated,\\static,
    \\sum,\\true,\\unallocated,\\valid,\\valid_function,\\valid_read,\\with},
  classoffset=0,
	alsoletter={\\},
	morecomment=[l]{//}
}

\lstloadlanguages{[ANSI]C,[Objective]Caml,csh,ACSL}

\lstdefinestyle{c}%
{language={[ANSI]C},alsolanguage=ACSL,style=frama-c-style}
\lstdefinestyle{c-basic}%
{language={[ANSI]C},alsolanguage=ACSL,style=frama-c-style,basicstyle=\lp@basic}

\newcommand{\listinginput}[3][1]%
{\lstinputlisting[style=c-basic,numbers=left,stepnumber=#1,firstnumber=#2]{#3}}
\newcommand{\listinginputcaption}[4][1]%
{\lstinputlisting[style=c-basic,numbers=left,stepnumber=#1,firstnumber=#2,caption={#3}]{#4}}

\lstnewenvironment{listing}[2][1]%
{\lstset{style=c-basic,numbers=left,stepnumber=#1,firstnumber=#2}}{}
\lstnewenvironment{listing-nonumber}%
{\lstset{style=c,numbers=none,basicstyle=\lp@basic}}{}

% Commands used mainly by Eva manual

\newcommand{\logwithrange}[2]%
{\lstinputlisting[breaklines=true,basicstyle=\ttfamily\small,linerange=#1]{#2}}

\newcommand{\cwithrange}[2]%
{\lstinputlisting[style=c-basic,numbers=left,linerange=#1]{#2}}

\newcommand{\csource}[1]%
{\lstinputlisting[style=c-basic,numbers=left]{#1}}

\lstnewenvironment{listing-log}%
{\lstset{numbers=none,basicstyle=\lp@basic}}{}


% ACSL + C (developers)
% --------------------------------------------------------------------------

\lstdefinestyle{framac-code}%
{language={[ANSI]C},alsolanguage=ACSL,style=frama-c-style,basicstyle=\lp@basic}

\newcommand{\cinput}[2][]%
{\lstinputlisting[
    language={[ANSI]C},
    alsolanguage=ACSL,
    style=frama-c-style,#1]{#2}
}
\newcommand{\cinline}[1]%
{\lstinline[style=framac-code]{#1}}

\lstnewenvironment{ccode}[1][]%
{\lstset{language={[ANSI]C},alsolanguage=ACSL,style=frama-c-style,basicstyle=\lp@basic,#1}}{}

% Configure
% --------------------------------------------------------------------------

\lstdefinelanguage{Configure}[]{csh}{%
  style=frama-c-shell-style,%
  morekeywords={fi},%
}

\newcommand{\configureinput}[1]%
{\lstinputlisting[language=Configure]{#1}}

\lstnewenvironment{configurecode}[1][]%
{\lstset{language=Configure,#1}}{}

% Commands
% --------------------------------------------------------------------------

\lstdefinelanguage{frama-c-commands}[]{}{%
  mathescape=false,%
  alsoletter=-.,%
  keywordstyle=\color{frama-c-green}\bfseries,%
  keywordstyle=[2]\color{frama-c-dark-red}\bfseries,%
  classoffset=0,%
  keywords={e-acsl-gcc.sh,frama-c,frama-c-gui,frama-c-script},%
  classoffset=1,%
  morekeywords={-load,-then,-then-last,-then-on,-then-replace,-save},%
  classoffset=0,%
  morestring=[b]{'},
  morestring=[b]{"},
  literate={\\\$}{\$}1%
}

\lstnewenvironment{frama-c-commands}[1][]
{\lstset{style=frama-c-basic-style,language=frama-c-commands,#1}}{}

% Dune
% --------------------------------------------------------------------------

\lstdefinelanguage{Dune}{%
  literate=%
    {à}{{\`a}}1%
    {é}{{\'e}}1%
  ,
  style=frama-c-style,%
  alsoletter=:-,%
  keywords={%
    action,alias,as,backend,context,default,deps,dune,executable,%
    env,env-vars,files,flags,from,generate_opam_files,install,%
    instrument_with,instrumentation,lang,libraries,library,name,optional,%
    package,plugin,profile,progn,public_name,rule,section,select,site,%
    targets,using%
  },%
  morekeywords=[2]{%
    :standard%
  },%
  morecomment=[l]{;},%
}

\lstdefinestyle{dune-basic}{%
  language=Dune,%
  style=frama-c-basic-style,%
  basicstyle=\lp@inline,%
}

\newcommand{\duneinput}[2][]{\lstinputlisting[style=dune-basic,#1]{#2}}

\lstnewenvironment{dunecode}[1][]{\lstset{style=dune-basic,#1}}{}

% Logs
% --------------------------------------------------------------------------

\lstdefinelanguage{Logs}[]{}{%
  style=frama-c-basic-style,
  mathescape=false,
  backgroundcolor=,
  literate={\\\$}{\$}1
}

\newcommand{\logsinput}[1]%
{\lstinputlisting[language=Logs,basicstyle=\lp@basic]{#1}}

\lstnewenvironment{logs}[1][]%
{\lstset{language=Logs,basicstyle=\lp@basic,#1}}{}

% Makefile
% --------------------------------------------------------------------------

\lstdefinelanguage{Makefile}[]{make}{%
  style=frama-c-shell-style,%
  morekeywords={include},%
}

\lstdefinestyle{make-basic}{%
  language=Makefile,%
  style=frama-c-basic-style,%
  basicstyle=\lp@inline,%
}

\newcommand{\makefileinput}[1]{\lstinputlisting[language=Makefile]{#1}}
\newcommand{\makeinput}[2][]{\lstinputlisting[style=make-basic,#1]{#2}}

\lstnewenvironment{makefilecode}[1][]%
{\lstset{language=Makefile,#1}}{}

\lstnewenvironment{makecode}[1][]%
{\lstset{style=make-basic,#1}}{}

% OCaml
% --------------------------------------------------------------------------

\lstdefinelanguage{Ocaml}[Objective]{Caml}{%
  style=frama-c-basic-style,%
  deletekeywords={when,module,struct,sig,begin,end},%
  morekeywords=[2]{failwith,raise,when},%
  morekeywords=[3]{module,struct,sig,begin,end},%
  literate=%
  {~}{${\scriptstyle\thicksim}$}1%
  {<}{$<$ }1%
  {>}{$>$ }1%
  {->}{$\rightarrow$ }1%
  {<-}{$\leftarrow$ }1%
  {:=}{$\leftarrow$ }1%
  {<=}{$\leq$ }1%
  {>=}{$\geq$ }1%
  {==}{$\equiv$ }1%
  {!=}{$\not\equiv$ }1%
  {<>}{$\neq$ }1%
  {'a}{$\alpha$ }1%
  {'b}{$\beta$ }1%
  {'c}{$\gamma$ }1%
  {µ}{`{}}1%
  {€}{\textbackslash}1%
  {à}{{\`a}}1%
  {é}{{\'e}}1%
}

\lstdefinestyle{ocaml-basic}{
  language=Ocaml,
  basicstyle=\lp@basic
}

\newcommand{\ocamlinput}[2][]{\lstinputlisting[style=ocaml-basic,#1]{#2}}

\lstnewenvironment{ocamlcode}[1][]{\lstset{style=ocaml-basic,#1}}{}

% Shell
% --------------------------------------------------------------------------

\lstdefinelanguage{Shell}[]{csh}{%
  escapechar=@
  identifierstyle=\lp@basic,
  mathescape=false,
  backgroundcolor=,
  literate={\\\$}{\$}1
}

\newcommand{\listingname}[1]%
{\colorbox{lstfile}{\footnotesize\sffamily File \bfseries #1}\vspace{-4pt}}

\lstnewenvironment{shell}[1][]
{\lstset{language=Shell,basicstyle=\lp@basic,#1}}{}

% Why
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
}

\lstdefinestyle{why-style}{%
  language=Why,%
  style=frama-c-basic-style,%
  basicstyle=\lp@inline,%
}

\newcommand{\whyinput}[1]%
{\lstinputlisting[style=why-style,basicstyle=\lp@basic]{#1}}
\newcommand{\whyinline}[1]%
{\lstinline[style=why-style]{#1}}

\lstnewenvironment{whycode}[1][]{\lstset{style=why-style,#1}}{}

% Default style is empty
% --------------------------------------------------------------------------

\lstset{style=frama-c-style}
