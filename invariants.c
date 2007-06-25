int a;
//@ global invariant a_is_positive: a > 0

typedef int T;
//@ type invariant T_is_positive(T x) { x > 0 } 

struct S {
  int f;
}
//@ type invariant S_f_is_positive(struct S s) { s.f > 0 } 
