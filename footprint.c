struct S {
  char *x;
  int *y;
}

//@ logic loc<void*> footprint(struct S s) { \union(s.x,s.y) }
