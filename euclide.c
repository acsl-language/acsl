/*@ requires x >= 0 && y >= 0;
  @ behavior bezoutProperty:
  @   ensures (*p)*x+(*q)*y == \result;
  @*/
int extended_Euclide(int x, int y, int *p, int *q) {
  int a = 1, b = 0, c = 0, d = 1;
  /*@ loop invariant x >= 0 && y >= 0 ;
    @ for bezoutProperty: loop invariant
    @    a*\at(x,Pre)+b*\at(y,Pre) == x && 
    @    c*\at(x,Pre)+d*\at(y,Pre) == y ;
    @ loop variant y;
    @*/
  while (y > 0) {
    int r = x % y;
    int q = x / y;
    int ta = a, tb = b;
    x = y; y = r;
    a = c; b = d;
    c = ta - c * q; d = tb - d * q;
  }
  *p = a; *q = b;
  return x;
}

