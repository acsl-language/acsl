int f (int n) {
  for (int i = 0; i < n; i++) {
  /*@ assert \at(i,LoopInit) == 0; */
  int j = 0;
  while (j++ < i) {
    /*@ assert \at(j,LoopInit) == 0; */
    /*@ assert \at(j,LoopCurrent) + 1 == j; */
    }
  }
}
