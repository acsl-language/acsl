//@ ghost int ghost_seq;
/*@ axiomatic SeqObserver { 
  @   logic \list<integer> observed_seq{L} reads ghost_seq; 
  @ }
  @*/

/*@ assigns ghost_seq;
  @ ensures register: observed_seq == (\old(observed_seq) ^ [| a |]);
  @*/
void observe(int a);

/*@ requires empty_seq: observed_seq == \Nil;
  @ assigns ghost_seq;
  @ ensures head_seq: \nth(observed_seq,0) == x;
  @ behavior shortest_seq:
  @   assumes no_loop_entrance: n<=0;
  @   ensures shortest_len: \length(observed_seq) == 2;
  @   ensures shortest_seq: observed_seq == [| x, z |];
  @ behavior longest_seq:
  @   assumes loop_entrance: n>0;
  @   ensures longest_len: \length(observed_seq) == 2+n;
  @   ensures longest_seq: 
  @     observed_seq == ([| x |] ^ ([| y |] *^ n) ^ [| z |]);
  @*/
void loops(int n, int x, int y, int z) {
  int i;
  //@ ghost observe(x);
  /*@ loop assigns i, ghost_seq;
    @ loop invariant id_min: 0<=i;
    @ loop invariant id_max: 0<=n ? i<=n : i<=0;
    @ loop invariant inv_seq: 
    @   observed_seq == (\at(observed_seq,LoopEntry) ^ ([| y |] *^ i)) ;  
    @*/
  for (i=0; i<n; i++) { 
    //@ ghost observe(y); 
    ;
  }
  //@ ghost observe(z);
}
