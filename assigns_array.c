/*@ assigns t[0..n-1];
    assigns *(t+(0..n-1));
    assigns *(t+{ i | int i ; 0 <= i < n }); */
void reset_array(int t[],int n) { 
  int i;
  for (i=0; i < n; i++) t[i] = 0;
}
