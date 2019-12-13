void m() {
  int k = 0;
  int array[6] = {1,2,3,6,7,8};
  /*@
    loop invariant 0 <= j <= 6;
    loop invariant k == \sum(0,j-1, \lambda int j; array[j]);
    loop variant 6 - j;
  @*/
  for (int j = 0; j < 6; j++) {
    int i = array[j];
    k += i;
  }
}
