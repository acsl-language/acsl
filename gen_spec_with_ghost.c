//@ ghost set<integer> forbidden = emptyset;

/*@ assigns forbidden;
  @ ensures ! Set::in(\result,\old(forbidden)
  @   && Set::in(\result,forbidden)
      && Set::subset(\old(forbidden),forbidden);
  @*/
int gen() {
  static int x = 0;
  /*@ data invariant I: \forall integer k;
    @    Set::mem(k,forbidden) ==> x > k;
    @*/
  x++;
  //@ ghost forbidden = Set::union(Set::single(x),forbidden);
  return x;
}
