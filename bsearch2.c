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
short bsearch(int t[], short n, int v) {
  short l = 0, u = n-1;
  /*@ loop invariant 0 <= l && u <= n-1;   
    @ for failure: loop invariant  
    @   \forall short k; 0 <= k < n => t[k] == v => l <= k <= u;
    @ loop variant u-l; 
    @*/
  while (l <= u ) {
    short m = l + (u-l)/2; // better than (u+l)/2
    if (t[m] < v) l = m + 1;
    else if (t[m] > v) u = m - 1;
    else return m; 
  }
  return -1;
}

