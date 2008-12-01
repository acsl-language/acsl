/*@ axiomatic Num_of_pos {
  @ logic integer num_of_pos{L}(integer i, integer j, double t[]);
  @
  @ axiom num_of_pos_empty{L} :
  @   \forall integer i, integer j, double t[];
  @       i > j ==> num_of_pos(i,j,t) == 0;
  @
  @
  @ axiom num_of_pos_true_case{L} :
  @   \forall integer i, integer j, double t[];
  @       i <= j && t[j] > 0.0 ==>
  @         num_of_pos(i,j,t) == num_of_pos(i,j-1,t) + 1;
  @
  @
  @ axiom num_of_pos_false_case{L} :
  @   \forall integer i, integer j, double t[];
  @       i <= j && ! (t[j] > 0.0) ==>
  @         num_of_pos(i,j,t) == num_of_pos(i,j-1,t);
  @ }
  @*/
