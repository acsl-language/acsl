

/* permut<L1,L2>(t1,t2,n) is true whenever t1[0..n-1] in state L1 
 * is a permutation of  t2[0..n-1] in state L2 
 */
//@ predicate permut<L1,L2>(double t1[], double t2[], integer n);
  

/*@ axiom permut_refl<L> :
  @   \forall double t[], integer n; permut<L,L>(t,t,n);
  @*/
 
/*@ axiom permut_sym<L1,L2> :
  @   \forall double [] t1, double t2[], integer n; 
  @     permut<L1,L2>(t1,t2,n) ==> permut<L2,L1>(t2,t1,n)
  @*/
 
/*@ axiom permut_trans<L1,L2,L3> :
  @   \forall double t1[], double t2[], double t3[];
  @     permut<l1,L2>(t1,t2) && permut<L2,L3>(t2,t3) 
  @     ==> permut<L1,L3>(t1,t3)
  @*/
  
/* axiom permut_exchange :
 *   forall t:int farray. forall i:int. forall j:int.
 *   permut(t, update(update(t,i,t[j]),j,t[i]));
 */


