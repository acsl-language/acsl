/*@ axiomatic NbOcc {
  @   // nb_occ(t,i,j,e) gives the number of occurrences of e in t[i..j]
  @   // (in a given memory state labelled L)
  @  logic integer nb_occ{L}(double t[], integer i, integer j, 
  @                          double e); 
  @  axiom nb_occ_empty{L}:
  @   \forall double t[], e, integer i, j;
  @     i > j ==> nb_occ(t,i,j,e) == 0;
  @  axiom nb_occ_true{L}:
  @   \forall double t[], e, integer i, j;
  @     i <= j && t[i] == e ==> 
  @       nb_occ(t,i,j,e) == nb_occ(t,i,j-1,e) + 1;
  @  axiom nb_occ_false{L}:
  @   \forall double t[], e, integer i, j;
  @     i <= j && t[i] != e ==> 
  @       nb_occ(t,i,j,e) == nb_occ(t,i,j-1,e);
  @ }
  @*/

