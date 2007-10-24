

/* permut<L1,L2>(t1,t2,n) is true whenever t1[0..n-1] in state L1 
 * is a permutation of  t2[0..n-1] in state L2 
 */
//@ predicate permut<L1,L2>(int t1[], int t2[], integer n);
  

/*@ axiom permut_refl<L> :
  @   \forall int t[]; \forall integer n; permut<L,L>(t,t,n)
  @*/
 
/*@ axiom permut_sym<L1,L2> :
  @   \forall int [] t1, int t2[]; \forall integer n; 
  @     permut<L1,L2>(t1,t2,n) -> permut<L2,L1>(t2,t1,n)
  @*/
 
axiom permut_trans :
  forall t1:int farray. forall t2:int farray. forall t3:int farray.
    (permut(t1,t2) and permut(t2,t3)) -> permut(t1,t3)
  
axiom permut_exchange :
  forall t:int farray. forall i:int. forall j:int.
    permut(t, update(update(t,i,t[j]),j,t[i]))


