/*@ axiomatic IntList {
  @  type int_list;
  @  logic int_list nil;
  @  logic int_list cons(integer n,int_list l);
  @  logic int_list append(int_list l1,int_list l2);
  @  axiom append_nil: 
  @   \forall int_list l; append(nil,l) == l;  
  @  axiom append_cons: 
  @   \forall integer n; int_list l1,l2; 
  @     append(cons(n,l1),l2) == cons(n,append(l1,l2));
  @ }
  @*/
