
int* f() {
  int a;
  return &a;
}

int* g() {
  int* p = f();
  //@ assert \dangling_contents{Here}(&p);
  return p+1;
}
