//NOPP-BEGIN
#include <stdlib.h> 

void frees_n_blocks(int *p[], unsigned n) {
  int **q=p;
  unsigned i;
//NOPP-END
/*@ assert \forall integer j; 0<=j<n ==> \freeable(q[j]); */
/*@ loop assigns   q[0..(i-1)];
  @ loop frees     q[0..\at(i-1,LoopCurrent)];
  @ loop invariant \forall integer j ;
                   0 <= j < i ==> \allocable(\at(q[j],LoopEntry));
  @ loop invariant \forall integer j ; 0 <= i <= n;
  @*/
  for (i=0; i<n; i++) {
    free(q[i]);
    q[i]=NULL;
  }
//NOPP-BEGIN
}
//NOPP-END
    

  
