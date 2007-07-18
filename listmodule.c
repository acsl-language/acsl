
/*@ module List :
  @ 
  @   type list<'a> = Nil | Cons('a , list<'a>);
  @
  @   logic integer length(list<'a> l) {
  @     \match l ; 
  @       | Nil : 0 
  @       | Cons(h,t) : 1+length(t)
  @   }
  @ 
  @   logic 'a fold_right(('a -> 'b -> 'b) f, list<'a> l,  'b acc) {
  @     \match l ;
  @       | Nil : acc
  @       | Cons(h,t) : f(h,fold(f,t,acc))
  @   }
  @
  @   logic list<'a> filter(('a -> boolean) f, list<'a> l) {
  @     fold_right((\lambda 'a x, list<'a> acc; 
  @       f(x) ? Cons(x,acc) : acc), Nil)
  @   }
  @*/

