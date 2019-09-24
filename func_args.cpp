/*@
  requires \valid(a[i..j-1]);
  requires \forall int k; \assigns(f,k) == \empty;  // requires f has no side-effects
  ensures \forall int k; k < i || k >= j; a[k] == \old(a[k]);
  ensures \forall int k; i <= k < j; \ensures(f, a[k], \old(a[k]));
*/
void m(int a[], int i, int j, int f(int) ) {
  for (int k = i; k<j; k++) a[k] = f(a[k]);
}
