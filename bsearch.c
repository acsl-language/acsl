/*@ requires 
  @   n >= 0 && \valid_range(t,0,n-1) &&
  @   t_is_sorted :: \forall short k1, short k2; 
  @       0 <= k1 <= k2 <= n-1 => t[k1] <= t[k2];
  @ assigns \nothing;
  @ behavior success:
  @   ensures \result >= 0 ==> t[\result] == v;
  @ behavior failure:
  @   ensures \result == -1 ==> 
  @     \forall short k; 0 <= k < n => t[k] != v;
  @*/
short bsearch(int t[], short n, int v);
