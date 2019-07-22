//@ type seq = integer[];

//@ logic seq init = { [ .. ] = 0 };

//@ logic seq ident = { init \with [0 .. 10] = \lambda integer i; i };

//@ lemma init_def: \forall integer i; init[i] == 0;

//@ lemma ident_def1: \forall integer i; i < 0 ==> ident[i] == 0;

//@ lemma ident_def2: \forall integer i; 0 <= i <= 10 ==> ident[i] == i;

//@ lemma ident_def3: \forall integer i; i > 10 ==> ident[i] == 0;
