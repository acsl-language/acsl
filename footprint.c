struct S {
  char *x;
  int *y;
};

//@ logic set<char*> footprint(struct S s) = \union(s.x,s.y) ;

/*@ axiom conversion: \forall S s;
      footprint(s) == \union(s.x,(char*) y + (0 .. sizeof(int) - 1); */
