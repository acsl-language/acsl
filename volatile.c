volatile int x;

/*@ ghost //@ requires p == &x;
  @ int reads_x(volatile int *p) { 
  @   static int injector_x[] = { 1, 2, 3 };
  @   static int injector_count = 0;
  @   if (p == &x) 
  @     return injector_x[injector_count++];
  @   else
  @     return 0; // should not happen
  @ }
  @*/

//@ ghost int collector_x[3];
//@ ghost int collector_count = 0;
  
/*@ ghost //@ requires p == &x;
  @ int writes_x(volatile int *p, int v) { 
  @   if (p == &x) 
  @     return collector_x[collector_count++] = v;
  @   else
  @    return 0; // should not happen
  @ }
  @*/

//@ volatile x reads reads_x writes writes_x;

/*@ ensures collector_count == 3 && collector_x[2] == 2;
  @ ensures \result == 6;
  @*/
int main () {
  int i, sum = 0;
  for (i=0 ; i < 3; i++) {
    sum += x;
    x = i;
  }
  return sum;
} 
