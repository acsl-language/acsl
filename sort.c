#include "permut.c"

/*@ predicate sorted{L}(double* t, int length) =
  \valid(t+(0..length -1)) &&
  \forall integer i,j; 0<=i<j< length ==> t[i] <= t[j];
*/

// implicitly, sorted(t,n) means sorted{Here}(t,n)

/*@ requires \valid(t+(0..n-1));
  @ ensures sorted(t,n) && permut{Pre,Here}(t,t,n);
  @*/
void sort(double t[], int n) {



}
