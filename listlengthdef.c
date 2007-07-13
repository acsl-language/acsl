/*@ logic integer list_length('a list l) {
  @    \match l ; 
  @      | Nil : 0 
  @      | Cons(h,t) : 1+list_length(t)
  @ }
  @*/
