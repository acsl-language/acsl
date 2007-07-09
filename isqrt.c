/*@ requires x >= 0;
  @ ensures \result >= 0;
  @ ensures \result * \result <= x;
  @ ensures x < (\result + 1) * (\result + 1);
  @*/
int isqrt(int x); 
