/* implementation */

int gen() {
  static int x = 0;
  //@ invariant I: \forall integer k; Set::mem(k,forbidden) ==> x > k; 
  return x++;
}

/* TODO

 the same can be done with a ghost field instead of a model field, by adding before the return :

  //@ ghost forbidden = union(single(\result),forbidden;

*/

  
