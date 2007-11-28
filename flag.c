typedef enum { BLUE, WHITE, RED } color;
/*@ type invariant isColor(color c) { 
  @   c == BLUE || c == WHITE || c == RED 
  @ }
  @*/

/*@ predicate isMonochrome(int t[], integer i, integer j, color c) {
  @   \valid(t+(i..j)) && 
  @   \forall integer k; i <= k <= j ==> t[k] == c 
  @ } 
  @*/

typedef struct flag {
  int n;
  color *colors;
} flag;

/*@ requires \valid(t+i) && \valid(t+j);
  @ assigns t[i],t[j];
  @ ensures t[i] == \old(t[j]) && t[j] == \old(t[i]);
  @*/
void swap(color t[], int i, int j) {
  int tmp = t[i];
  t[i] = t[j];
  t[j] = tmp;
}

/*@ type invariant is_colored(flag f) {
  @   f.n >= 0 && \valid(f.colors+(0..f.n-1)) &&
  @   \forall integer k; 0 <= k < f.n ==> isColor(f.colors[k])
  @ }
  @*/

/*@ assigns f.colors[0..f.n-1];
  @ ensures 
  @   \exists integer b, integer r; 
  @      isMonochrome(f.colors,0,b-1,BLUE) &&
  @      isMonochrome(f.colors,b,r-1,WHITE) &&
  @      isMonochrome(f.colors,r,f.n-1,RED))
  @*/
void flag(flag f) {
  color *t = f.colors;
  int b = 0;
  int i = 0;
  int r = f.n;
  /*@ invariant
    @   (\forall integer k; 0 <= k < f.n ==> isColor(t[k])) &&
    @   0 <= b <= i <= r <= f.n &&
    @   isMonochrome(t,0,b-1,BLUE) &&
    @   isMonochrome(t,b,i-1,WHITE) &&
    @   isMonochrome(t,r,f.n-1,RED);
    @ loop_assigns b,i,r,t[0 .. f.n-1];
    @ variant r - i;
    @*/
  while (i < r) {
    switch (t[i]) {
    case BLUE:  
      swap(t, b++, i++);
      break;	    
    case WHITE: 
      i++; 
      break;
    case RED: 
      swap(t, --r, i);
      break;
    }
  }
}
