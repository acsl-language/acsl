/*@ assigns \nothing;
  @ ensures \result > x;
  @*/
int increment(int x) { return x + 1; }
/*@ assigns \nothing;
  @ ensures \result < x;
  @*/
int decrement(int x) { return x - 1; }

int foo(bool b) {
  int (*fp)(int) = b ? increment : decrement;
  int y = fp(4);
  //@ assert y != 4;
}
