int a;
//@ data invariant a_is_positive: a >= 0 ;

typedef double temperature; 
/*@ strong type invariant temp_in_celsius(temperature t) =
  @   t >= -273.15 ;
  @*/

struct S {
  int f;
};
//@ type invariant S_f_is_positive(struct S s) = s.f >= 0 ;
