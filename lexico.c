//@ ensures \result >= 0
int dummy();

//@ type intpair = (integer,integer)

/*@ predicate lexico(intpair p1, intpair p2) =
  @   \let (x1,y1) = p1 ;
  @   \let (x2,y2) = p2 ;
  @      x1 < x2 && 0 <= x2 || 
  @      x1 == x2 && 0 <= y2 && y1 < y2;
  @*/

//@ requires x >= 0 && y >= 0;
int f(int x,int y) {
  /*@ loop invariant x >= 0 && y >= 0;
    @ loop variant (x,y) for lexico;
    @*/
  while (x > 0 && y > 0) {
    
    if (dummy()) {
      x--; y = dummy();
    }
    else y--;
  }
}
