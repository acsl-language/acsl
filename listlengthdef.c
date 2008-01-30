/*@ logic integer list_length<A>(list<A> l) =
  @    \match l ;
  @      | Nil : 0
  @      | Cons(h,t) : 1+list_length(t) ;
  @*/
