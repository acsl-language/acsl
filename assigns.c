struct list {
  int hd;
  struct list *next;
};

//@ assigns *p;
void reset(int *p) { *p = 0; }

// three equivalent assigns clauses
//@ assigns t[0..n-1];
//@ assigns *(t+(0..n-1));
//@ assigns *(t+{ i | int i ; 0 <= i < n });
void reset_array(int t[],int n) { 
  int i;
  for (i=0; i < n; i++) t[i] = 0;
}

//@ assigns { p->hd | struct list *p ; reachable(root,p) }
void incr_list(struct list *p) {
  while (p) { p->hd++ ; p = p->next; }
}
