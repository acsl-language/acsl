int f (int x, int y) {
  //@ ghost int z = x + y;
  switch (x) {
  case 0: return y;
  //@ ghost 1: z=y;
  // above statement is correct.
  //@ ghost 2: { z++; break; }
  // invalid, would bypass the non-ghost default
  default: y++;
  }
  return y;
}

int g(int x) {
  //@ ghost int z = x;
  if (x > 0) { return x; }
  //@ ghost else { z++; return x; }
  // invalid, would bypass the non-ghost return
  return x+1;
}
