double total = 0.0;

/*@ requires n >= 0 && \valid(t+(0..n-1)) ;
  @ assigns total
      \from t[0..n-1] = total + \sum(0,n-1,\lambda int k; t[k]);
  @*/
void array_sum(double t[],int n) {
  int i;
  for(i=0; i < n; i++) total += t[i];
  return;
}
