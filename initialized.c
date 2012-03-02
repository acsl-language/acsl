int f(int n) {
  int x;

  if (n > 0) x = n ; else x = -n;
  //@ assert \initialized{Here}(&x);
  return x;
}
