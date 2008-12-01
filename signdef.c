//@ predicate is_positive(integer x) = x > 0;
/*@ logic integer sign(real x) =
  @   x > 0.0 ? 1 : ( x < 0.0 ? -1 : 0);
  @*/
