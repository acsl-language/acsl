/*@ logic integer list_length<A>(list<A> l) =
  @    \match l {
  @      case Nil : 0
  @      case Cons(h,t) : 1+list_length(t) 
  @    };
  @*/
