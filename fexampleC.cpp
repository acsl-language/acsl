int x;

/*@ assigns x;
  @ ensures x == \old(x+a);
  @*/
void increment(int a) { x+=a; }

void test() {
  void (*fp)(int) = increment;
  fp(2);
  fp(-1);
  //@ assert x == \old(x+1);
}
