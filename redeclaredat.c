int x;
int y;

void m() {
  y = 1;
  x = 4;
b: ; // a label can't be directly over a declaration, hence the ';'.
  //@ assert \at(x,b) == 4;
  int* x = &y;
  y = 2;
c:
  y = 3;
  //@ assert \at(x,b) == 4;
  //@ assert *x == 3;
  //@ assert \at(*x,c) == 2;
  *x = 5;
}
