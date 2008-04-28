/* implementation */

int gen() {
  static int x = 0;
  /*@ global invariant I: \forall integer k;
    @    Set::mem(k,forbidden) ==> x > k;
    @*/
  return x++;
}
