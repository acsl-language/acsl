/* bsearch(t,n,v) search for element v in array t 
   between index 0 and n-1
   array t is assumed sorted in increasing order
   returns an index i between 0 and n-1 where t[i] equals v, 
   or -1 if no element of t is equal to v  
 */
/*@ requires 
  @   n >= 0 && \valid_range(t,0,n-1) &&
  @   \forall short k1, short k2; 0 <= k1 <= k2 <= n-1 => t[k1] <= t[k2];
  @ behavior success:
  @   ensures \result >= 0 ==> t[\result] == v;
  @ behavior failure:
  @   ensures \result == -1 ==> \forall short k; 0 <= k < n => t[k] != v;
  @*/
short bsearch(int t[], short n, int v);
