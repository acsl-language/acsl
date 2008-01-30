/*@ requires n > 0 && \valid(t+(0..n-1));
  @ ensures \result = \max(0,n-1,(\lambda integer k ; t[k]));
  @*/
double max(double t[], int n) {
  int i = 0; double m,v;
  do {
    v = t[i++];
    m = v > m ? v : m;
  }
  /*@ invariant m == \max(0,i-1,(\lambda integer k ; t[k]));
    @*/
  while (i < n);
  return m;
}
