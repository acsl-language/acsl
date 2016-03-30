//@ ghost int ghost_trace;
/*@ axiomatic TraceObserver { 
  @   logic \list<integer> observed_trace{L} reads ghost_trace; 
  @ }
  @*/

/*@ assigns ghost_trace;
  @ ensures register: observed_trace == (\old(observed_trace) ^ [| a |]);
  @*/
void track(int a);

/*@ requires empty_trace: observed_trace == \Nil;
  @ assigns ghost_trace;
  @ ensures head_seq: \nth(observed_trace,0) == x;
  @ behavior shortest_trace:
  @   assumes no_loop_entrance: n<=0;
  @   ensures shortest_len: \length(observed_trace) == 2;
  @   ensures shortest_seq: observed_trace == [| x, z |];
  @ behavior longest_trace:
  @   assumes loop_entrance: n>0;
  @   ensures longest_len: \length(observed_trace) == 2+n;
  @   ensures longest_seq: 
  @     observed_trace == ([| x |] ^ ([| y |] *^ n) ^ [| z |]);
  @*/
void loops(int n, int x, int y, int z) {
  int i;
  //@ ghost track(x);
  /*@ loop assigns i, ghost_trace;
    @ loop invariant idx_min: 0<=i;
    @ loop invariant idx_max: 0<=n ? i<=n : i<=0;
    @ loop invariant inv_seq: 
    @   observed_trace == (\at(observed_trace,LoopEntry) ^ ([| y |] *^ i));  
    @*/
  for (i=0; i<n; i++) { 
    //@ ghost track(y); 
    ;
  }
  //@ ghost track(z);
}
