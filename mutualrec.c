

//@ decreases n;
int even(int n) {
  if (n == 0) return TRUE;
  return odd(n-1);
}

//@ decreases x;
int odd(int x) {
  if (x == 0) return FALSE;
  return even(x-1);
}
