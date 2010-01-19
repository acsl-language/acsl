/*@ axiomatic sign {
  @   logic integer get_sign(real x);
  @   axiom sign_pos: \forall real x; x >= 0. ==> get_sign(x) == 1;
  @   axiom sign_neg: \forall real x; x <= 0. ==> get_sign(x) == -1;
  @ }
  @*/
