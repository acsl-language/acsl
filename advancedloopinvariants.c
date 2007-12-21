/*@ requires n > 0;
  @ ensures \result == \max(t,0,n-1);
  @*/
double max_array(double t[], int n) {
  double m;
  goto L;
  for (int i=1 ; i < n ; i++) {
    if (t[i] <= m) continue;
  L: m = t[i];    
  }
  return m;
}
