/*@ logic integer num_of_pos<L>(int i,int j, double t[]) 
  @
  @ axiom num_of_pos_empty<L> :
  @   \forall int i, j, double t[];
  @       i > j ==> num_of_pos<L>(i,j,t) == 0
  @
  @ axiom num_of_pos_true_case<L> :
  @   \forall int i, j, double t[];
  @       i <= j && \at(t[j],L) > 0.0 ==> 
  @         num_of_pos<L>(i,j,t) == num_of_pos<L>(i,j-1,t) + 1;
  @
  @ axiom num_of_pos_false_case<L> :
  @   \forall int i, j, double t[];
  @       i <= j && ! (\at(t[j],L) > 0) ==> 
  @         num_of_pos(i,j,t) == num_of_pos(i,j-1,t);
  @*/
