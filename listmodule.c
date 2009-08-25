
/*@ module List {
  @
  @   type list<A> = Nil | Cons(A , list<A>);
  @
  @   logic integer length<A>(list<A> l)  =
  @     \match l {
  @       case Nil : 0
  @       case Cons(h,t) : 1+length(t) } ;
  @
  @   logic A fold_right<A,B>((A -> B -> B) f, list<A> l, B acc) =
  @     \match l {
  @       case Nil : acc
  @       case Cons(h,t) : f(h,fold_right(f,t,acc)) } ;
  @
  @   logic list<A> filter<A>((A -> boolean) f, list<A> l) =
  @     fold_right((\lambda A x, list<A> acc;
  @       f(x) ? Cons(x,acc) : acc), Nil) ;
  @
  @ }
  @*/
