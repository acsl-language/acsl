

/* nb_occ<L>(t,i,j,e) gives the number of occurrences of e in t[i..j]
 * at some label L
 */

//@ logic integer nb_occ<L>(double t[], integer i, integer j, double e);

/*@ axiom nb_occ_empty<L> :
  @   \forall double t[], integer i, integer j, double e;
  @     i > j ==> nb_occ<L>(t,i,j,e) == 0;
  @*/

/*@ axiom nb_occ_true<L> :
  @   \forall double t[], integer i, integer j, double e;
  @     i <= j && \at(t[i],L) == e ==> 
  @       nb_occ<L>(t,i,j,e) == nb_occ<L>(t,i,j-1,e) + 1;
  @*/

/*@ axiom nb_occ_false<L> :
  @   \forall double t[], integer i, integer j, double e;
  @     i <= j && \at(t[i],L) != e ==> 
  @       nb_occ<L>(t,i,j,e) == nb_occ<L>(t,i,j-1,e);
  @*/

