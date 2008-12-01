struct S {
  char *x;
  int *y;
};

//@ logic set<char*> footprint(struct S s) = \union(s.x,s.y) ;

/*@ logic set<char*> footprint2(struct S s) =
  @    \union(s.x,(char*)s.y+(0..sizeof(s.y)-1)) ;
  @*/

/*@ axiomatic Conv {
    axiom conversion: \forall struct S s;
      footprint(s) == \union(s.x,(char*) y + (0 .. sizeof(int) - 1));
    }
*/
