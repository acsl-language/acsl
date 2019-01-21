typedef int (*II)(int); // int->int

/*@ requires \true;
  @ assigns \nothing;
  @ ensures \result == x+1;
  @*/
int increment(int x) { return x + 1; }

/*@ requires \requires(f,x);
  @ assigns \assigns(f,x);
  @ ensures \ensures(f,\result,x);
  @*/
int doOnce(II f, int x) {
   return f(x);
}

/*@ requires \requires(f,x) && (\forall int t; \ensures(f,t,x) ==> \requires(f,t));
  @ assigns \assigns(f,x), (\union int t: \ensures(f,t,x); \assigns(f,t));
  @ ensures \exists int t; \ensures(f,t,x) && \ensures(f,\result,t);
  @*/
int doTwice(II f, int x) {
   return f(f(x));
}

int test() {
  int y = doOnce(increment,42);
  //@ assert y == 43;
  y = doTwice(increment,42);
  //@ assert y == 44;
}
