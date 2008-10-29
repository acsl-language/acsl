/*@ axiomatic sign {
  @   logic integer sign(real x);
  @   axiom sign_pos: \forall real x; x >= 0 ==> sign(x) == 1;
  @   axiom sign_neg: \forall real x; x <= 0 ==> sign(x) == -1;
  @ }
  @*/
