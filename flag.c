typedef enum { BLUE, WHITE, RED } color;
/*@ type invariant isColor(color c) =
  @   c == BLUE || c == WHITE || c == RED ;
  @*/

/*@ predicate permut{L1,L2}(color t1[], color t2[], integer n)
  @   reads \at(t1[..],L1), \at(t2[..],L2);
  @*/

/*@ requires \valid(t+i) && \valid(t+j);
  @ assigns t[i],t[j];
  @ ensures t[i] == \old(t[j]) && t[j] == \old(t[i]);
  @*/
void swap(color t[], int i, int j) {
  int tmp = t[i];
  t[i] = t[j];
  t[j] = tmp;
}

typedef struct flag {
  int n;
  color *colors;
} flag;
/*@ type invariant is_colored(flag f) =
  @   f.n >= 0 && \valid(f.colors+(0..f.n-1)) &&
  @   \forall integer k; 0 <= k < f.n ==> isColor(f.colors[k]) ;
  @*/

/*@ predicate isMonochrome{L}(color t[], integer i, integer j, 
  @                           color c) =
  @   \forall integer k; i <= k <= j ==> t[k] == c ;
  @*/

/*@ assigns f.colors[0..f.n-1];
  @ ensures 
  @   \exists integer b, integer r; 
  @      isMonochrome(f.colors,0,b-1,BLUE) &&
  @      isMonochrome(f.colors,b,r-1,WHITE) &&
  @      isMonochrome(f.colors,r,f.n-1,RED) &&
  @      permut{Old,Here}(f.colors,f.colors,f.n-1);
  @*/
void dutch_flag(flag f) {
  color *t = f.colors;
  int b = 0;
  int i = 0;
  int r = f.n;
  /*@ loop invariant
    @   (\forall integer k; 0 <= k < f.n ==> isColor(t[k])) &&
    @   0 <= b <= i <= r <= f.n &&
    @   isMonochrome(t,0,b-1,BLUE) &&
    @   isMonochrome(t,b,i-1,WHITE) &&
    @   isMonochrome(t,r,f.n-1,RED) &&
    @   permut{Pre,Here}(t,t,f.n-1);
    @ loop assigns b,i,r,t[0 .. f.n-1];
    @ loop variant r - i;
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
