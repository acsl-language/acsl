//@ ghost set<integer> forbidden = \empty;

/*@ assigns forbidden;
  @ ensures ! \subset(\result,\old(forbidden))
  @   && \result \in forbidden
      && \subset(\old(forbidden),forbidden);
  @*/
int gen() {
  static int x = 0;
  /*@ global invariant I: \forall integer k;
    @    k \in forbidden ==> x > k;
    @*/
  x++;
  //@ ghost forbidden = \union(x,forbidden);
  return x;
}
