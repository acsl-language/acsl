#include <iostream>
#include <algorithm>

class FF {
public:
  int value;
  /*@ assigns value; ensures value == v; */
  FF(int v) { value = v; }

  /*@ assigns \empty; ensures \result == (v == value); */
  bool operator()(int v) { return v == value; }
};

int main() {
   int a[] = {1,2,3,4,5};

   int value = 3;
   bool b1 = std::any_of(a,&a[5],/*@(FF)@*/[value](int v){ return v == value; });
   value = 6;
   bool b2 = std::any_of(a,&a[5],/*@(FF)@*/[value](int v){ return v == value; });
   std::cout << b1 << " " << b2 << std::endl;
}

