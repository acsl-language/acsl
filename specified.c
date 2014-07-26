
int* f() {
  int a;
  return &a;
}

int* g() {
  int* p = f();
  //@ assert \specified{Here}(&p);
  return p+1;
}
