struct list {
  int hd;
  struct list *next;
}

/*@ logic reachable(struct list *from, struct list *to) 
  @   reads from->next;
  @*/

//@ assigns { p->hd | struct list *p ; reachable(root,p) } ;
void incr_list(struct list *p) {
  while (p != null) { p->hd++ ; p = p->next }
}
