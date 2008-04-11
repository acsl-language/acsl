/*@ requires n > 0;
    requires \forall int i; 0<= i <= n-1 ==> \valid(p + i);
    assigns \nothing;
    ensures \forall int i; 0 <= i <= n-1 ==> \result >= p[i];
    ensures \exists int i; 0 <= i <= n-1 && \result == p[i];
*/
int max_seq(int* p, int n);

int max_seq(int* p, int n) {
  int res = *p;
  int i;
  /*@ ghost int idx = 0; */
  /*@ loop invariant \forall integer j; 0 <= j <= i ==> res >= *(p+j);
      loop invariant \valid(p+idx) && *(p+idx) == res;
  */
  for(i = 0; i < n; i++) {
    if (res < *p) {
      res = *p;
      /*@ ghost idx = i;*/
    }
    p++;
  }
  return res;
}
