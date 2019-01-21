/*@ assigns \nothing;
  @ ensures \result >= x;
  @*/
int increment(int x) { return x + 1; }

int main() {
  int (*fp)(int) = increment;
  int y = fp(4);
  //@ assert y >= 4;
}
