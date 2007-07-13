
/*@ logic module List
  @ 
  @   type 'a list = Nil | Cons of 'a * 'a list;
  @
  @   integer length('a list l) {
  @     \match l ; 
  @       | Nil : 0 
  @       | Cons(h,t) : 1+length(t)
  @   }
  @ 
  @   'a fold_right(('a -> 'b -> 'b) f, 'a list l,  'b acc) {
  @     \match l ;
  @       | Nil : acc
  @       | Cons(h,t) : f(h,fold(f,t,acc))
  @   }
  @
  @   'a list filter(('a -> boolean) f, 'a list l) {
  @     fold_right((\lambda 'a x, 'a list acc; 
  @       f(x) ? Cons(x,acc) : acc), Nil)
  @   }
  @*/

