

/* nb_occ(t,i,j,e) gives the number of occurrences of e in t[i..j]
 * (in a given memory state labelled L)
 */

/*@ logic integer nb_occ{L}(double t[], integer i, integer j, 
  @                         double e) 
  @   reads t[..];
  @*/
/* Notice that without label {L}, t[..] would be rejected. 
 * With {L}, it is indeed a shortcut for \at(t[..],L).
 */

/*@ axiom nb_occ_empty{L} :
  @   \forall double t[], integer i, integer j, double e;
  @     i > j ==> nb_occ(t,i,j,e) == 0;
  @*/
// without {L}, term nb_occ(t,i,j,e) would be rejected 

/*@ axiom nb_occ_true{L} :
  @   \forall double t[], integer i, integer j, double e;
  @     i <= j && t[i] == e ==> 
  @       nb_occ(t,i,j,e) == nb_occ(t,i,j-1,e) + 1;
  @*/
// without {L}, term t[i] would be rejected, here it is \at(t[i],L)

/*@ axiom nb_occ_false{L} :
  @   \forall double t[], integer i, integer j, double e;
  @     i <= j && t[i] != e ==> 
  @       nb_occ<L>(t,i,j,e) == nb_occ<L>(t,i,j-1,e);
  @*/

