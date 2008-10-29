
// this time, the specification accepts circular lists, but does not ensure
// that the function terminates on them (as a matter of fact, it does not).
/*@ assigns { q->hd | struct list *q ; reachable(p,q) } ;
  @ terminates reachable(p,NULL);
  @*/
void incr_list(struct list *p) {
  while (p) { p->hd++ ; p = p->next; }
}
