/*@ logic integer num_of_pos(int i,int j, double t[]) reads t[i]
  @
  @ axiom num_of_pos_empty :
  @   \forall int i, int j, double t[];
  @       i > j ==> num_of_pos(i,j,t) == 0
  @
  @ axiom num_of_pos_true_case :
  @   \forall int i, int j, int k, int t[];
  @       i <= j && t[j] > 0.0 ==> 
  @         num_of_pos(i,j,t) == num_of_pos(i,j-1,t) + 1;
  @
  @ axiom num_of_pos_false_case :
  @   \forall int i, int j, int k, int t[];
  @       i <= j && ! (t[j] > 0) ==> 
  @         num_of_pos(i,j,t) == num_of_pos(i,j-1,t);
  @*/
