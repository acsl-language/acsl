/*@ axiomatic Nb_occ {
  @ logic integer nb_occ{L}(double t[], integer i, integer j,
  @                         double e)
  @      reads t[i..j];
  @
  @ axiom nb_occ_empty{L}: // ...
//NOPP-BEGIN
     \forall double t[], integer i,j, double e;
       i>j ==> nb_occ(t,i,j,e) == 0;
//NOPP-END
  @
  @ // ...
  @ }
  @*/
