/*@ behavior result_ge_x: 
  @   ensures \result >= x ;
  @ behavior result_ge_y: 
  @   ensures \result >= y; 
  @ behavior result_is_lub:
  @   ensures \forall integer z ; z >= x && z >= y ==> z >= \result;
  @*/
int max(int x, int y);
