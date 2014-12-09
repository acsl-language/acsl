
int* f() {
  int a;
  return &a;
}

int* g() {
  int* p = f();
  //@ assert \dangling{Here}(&p);
  return p+1;
}
