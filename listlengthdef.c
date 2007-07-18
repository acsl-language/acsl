/*@ logic integer list_length(list<'a> l) {
  @    \match l ; 
  @      | Nil : 0 
  @      | Cons(h,t) : 1+list_length(t)
  @ }
  @*/
