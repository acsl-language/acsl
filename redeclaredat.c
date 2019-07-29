int x;
int y;

void m() {
  y = 1;
  x = 4;
  b:
  { 
    //@ assert \at(x,b) == 4;
    int* x = &y;
    y = 2;
    c:
    y = 3;
    //@ assert \at(x,b) == 4;
    //@ assert *x == 3;
    //@ assert \at(*x,c) == 1;
   }
}
