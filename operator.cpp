class Negator {
  /*@ requires \true;
    @ assigns \nothing;
    @ ensures \result == -x;
    @*/
  int operator()(int x);
};
