/* implementation */

int gen() {
  static int x = 0;
  /*@ data invariant I: \forall integer k; 
    @    Set::mem(k,forbidden) ==> x > k; 
    @*/
  return x++;
}



  
