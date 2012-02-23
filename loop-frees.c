//NOPP-BEGIN
#include <stdlib.h> 

void frees_n_blocks(int *p[], size_t n) {
  int **q=p;
  size_t i=0;
//NOPP-END
//@ ghost L0: 
/*@ loop assigns   q[0..i];
  @ loop frees \at(q[0..\at(i,Here)],L0);
  @*/
  while (i<n) {
    free(q[i]);
    q[i]=NULL;
  }
//NOPP-BEGIN
}
//NOPP-END
    

  
