verbatimtex
%&latex
\documentclass[a4paper,11pt,twoside,openright]{report}
\usepackage[T1]{fontenc}
\usepackage{times}
\usepackage{color}
\input{macros}
\begin{document}
etex

input boxes

vardef fleche(expr p) =
  drawarrow p withcolor blue;
  point .5*length p of p
enddef;

vardef yellownodes(text t) =
    forsuffixes a=t:
      fill bpath a withcolor red+green;
    endfor;
    drawboxed(t);
  enddef;
  
  beginfig(1);
  circleit.init(btex ~~~ etex) ;
  circleit.loop(btex ~~~ etex) ;
  circleit.inv(btex inv etex) ;
  circleit.loopend(btex ~~~ etex) ;
  circleit.test(btex do etex) ;
  circleit.exit(btex ~~~ etex) ;
  loopend.c - exit.c =
  inv.c - loopend.c = 
  loop.c - inv.c = 
  init.c - loop.c = (0,40pt) ;
  inv.c - test.c = (100pt,0);
  yellownodes(init,loop,inv,loopend,test,exit) ;
  pickup pencircle scaled 1pt;
  label.rt(btex $i\la 0$ etex, fleche(init.s -- loop.n)) ;
  label.rt(btex $m\la t[i]$ etex, fleche(loop.s -- inv.n)) ;
  label.rt(btex $i\la i+1$ etex, fleche(inv.s -- loopend.n)) ;
  label.rt(btex $i\geq n$ etex, fleche(loopend.s -- exit.n)) ;
  label.urt(btex $i < n$ etex, fleche(loopend.w{left} .. {up}test.s)) ;
  label.top(btex $m < t[i]$ etex, fleche(test.n{up} .. {right}loop.w)) ;
  label.top(btex $m\geq t[i]$ etex, fleche(test.e -- inv.w)) ;
  
endfig;


end
