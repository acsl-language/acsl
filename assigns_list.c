struct list {
  int hd;
  struct list *next;
}

// reachability in NULL-terminated lists
/*@ predicate reachable(struct list *from, struct list *to) {
  @   from == to || from != \null && reachable(from->next,to)
  @ }
  @*/

//@ assigns { q->hd | struct list *q ; reachable(p,q) } ;
void incr_list(struct list *p) {
  while (p != null) { p->hd++ ; p = p->next }
}
