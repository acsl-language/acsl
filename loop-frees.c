//NOPP-BEGIN
#include <stdlib.h> 

void frees_n_blocks(int *p[], unsigned n) {
  int **q=p;
  unsigned i;
//NOPP-END
/*@ loop assigns   q[0..i];
  @ loop frees     q[0..\at(i,LoopCurrent)];
  @ loop invariant \forall integer j ;
                   0 <= j < i ==> \allocable(\at(q[j],LoopEntry));
  @ loop invariant \forall integer j ;
                   i <= j < n ==> \freeable(q[j]);
  @ loop invariant \forall integer j ; 0 <= i <= n;
  @*/
  for (i=0; i<n; i++) {
    free(q[i]);
    q[i]=NULL;
  }
//NOPP-BEGIN
}
//NOPP-END
    

  
