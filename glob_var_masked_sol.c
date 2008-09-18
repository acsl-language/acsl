int x;

//@ ghost int* const ghost_ptr_x = &x;

//@ assigns x;
int g();

//@ assigns *ghost_ptr_x;
int f(int x) {
  // ...
  return g();
}
