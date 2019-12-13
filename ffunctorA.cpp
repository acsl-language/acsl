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

   bool b1 = std::any_of(a,&a[5],FF(3)); // true - there is a 3 in the list
   bool b2 = std::any_of(a,&a[5],FF(6)); // false - there is no 6
   std::cout << b1 << " " << b2 << std::endl;
}

