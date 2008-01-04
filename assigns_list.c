struct list {
  int hd;
  struct list *next;
};

// reachability in NULL-terminated lists
/*@ predicate reachable(struct list *root, struct list *to) {
  @   root == to || root != \null && reachable(root->next,to)
  @ }
  @*/

//@ assigns { q->hd | struct list *q ; reachable(p,q) } ;
void incr_list(struct list *p) {
  while (p) { p->hd++ ; p = p->next; }
}
