struct list {
  int hd;
  struct list* next;
};

// We give an axiomatic definition of the reachability predicate,
// which is equivalent to the definition seen above.
/*@ predicate reachable(struct list* root, struct list* to); */
/*@ axiom reachable_self: \forall struct list* p; reachable(p,p); */
/*@ axiom reachable_next{L}:
      \forall struct list* root,*to;
      \valid(root) && reachable(root->next,to) ==>
          reachable(root,to); */

// this time, the specification accepts circular lists, but does not ensure
// that the function terminates on them (as a matter of fact, it does not).
/*@ assigns { q->hd | struct list *q ; reachable(p,q) } ;
    terminates reachable(p,\null);
*/
void incr_list(struct list *p) {
  while (p) { p->hd++ ; p = p->next; }
}
