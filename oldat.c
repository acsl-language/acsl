int i;
int t[10];

//@ ensures 0 <= \result <= 9;
int any();

/*@ assigns i,t[\at(i,Post)]
  @ ensures
  @   t[i] == \old(t[\at(i,Here)]) + 1;
  @ ensures 
  @   \let j = i; t[j] == \old(t[j]) + 1;
  @*/
void f() {
  i = any();
  t[i]++;
}

