struct list {
  int hd;
  struct list *next;
};

//NOPP-BEGIN
// reachability in linked lists
/*@ inductive reachable{L}(struct list *root, struct list *to) {
  @   case empty: \forall struct list *l; reachable(l,l) ;
  @   case non_empty: \forall struct list *l1,*l2;
  @      \valid(l1) && reachable(l1->next,l2) ==> reachable(l1,l2) ;
  @ }
*/
//NOPP-END
//@ assigns *p;
void reset(int *p) { *p = 0; }

// three equivalent assigns clauses
/*@ assigns t[0..n-1];
  @ assigns *(t+(0..n-1));
  @ assigns *(t+{ i | int i ; 0 <= i < n }); */
void reset_array(int t[],int n) {
  int i;
  for (i=0; i < n; i++) t[i] = 0;
}

//@ assigns { q->hd | struct list *q ; reachable(p,q) };
void incr_list(struct list *p) {
  while (p) { p->hd++ ; p = p->next; }
}
