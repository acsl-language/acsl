//NOPP-BEGIN
int odd(int x);
//NOPP-END
/*@
  requires n>=0;
  decreases n;
*/
int even(int n) {
  if (n == 0) return 1;
  return odd(n-1);
}

/*@
  requires n>=0;
  decreases x;
*/
int odd(int x) {
  if (x == 0) return 0;
  return even(x-1);
}
