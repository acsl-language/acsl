struct list {
  int hd;
  struct list *next;
};

// reachability in NULL-terminated lists
/*@ predicate reachable{L}(struct list *root, struct list *to) =
  @   root == to || root != \null && reachable(root->next,to) ;
  @*/

// The requires clause forbids to give a circular list
/*@ requires reachable(p,\null);
  assigns { q->hd | struct list *q ; reachable(p,q) } ;
*/
void incr_list(struct list *p) {
  while (p) { p->hd++ ; p = p->next; }
}
