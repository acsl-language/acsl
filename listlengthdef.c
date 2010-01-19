//NOPP-BEGIN
//@ type list<A> = Nil | Cons(A , list<A>);
//NOPP-END
/*@ logic integer list_length<A>(list<A> l) =
  @    \match l {
  @      case Nil : 0
  @      case Cons(h,t) : 1+list_length(t)
  @    };
  @*/
