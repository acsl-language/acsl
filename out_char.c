void out_char(char c) {
  static int col = 0;
  //@ global invariant I : 0 <= col <= 79;
  col++;
  if (col >= 80) col = 0;
}
