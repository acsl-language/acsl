/*@ behavior p_changed:
  @   assumes n > 0; 
  @   assigns *p;
  @   ensures *p == n;
  @ behavior q_changed:
  @   assumes n <= 0;
  @   assigns *q;
  @   ensures *q == n;
  @*/
void f(int n, int *p, int *q) {
  if (n > 0) *p = n; else *q = n;
}
