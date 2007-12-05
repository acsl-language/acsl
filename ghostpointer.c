
void f(int x, int *q) {
  //@ ghost int *p = q;
  //@ ghost *p = 0;  
  // above assignment is wrong: it modifies *q which lies 
  // in regular memory heap
  
  //@ ghost p = &x;  
  //@ ghost *p = 0;  
  // above assignment is wrong: it modifies x which lies 
  // in regular memory stack
  
}
