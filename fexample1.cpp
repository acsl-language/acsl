#include <stdio.h>
#include <iostream>
#include <stdlib.h>

int f(int k) { return k + 1; }
int ff(int k) { return k + 1; }
int f2(int k,int t) { return k + 1; }

class P {
  public:
   int n;
   P(int x) { n = x; }
   int g() { return 1 + n; }
   int h() { return 1 + n; }
};

class Q {
  public:
   int operator()(int x) { return x + 2; }
};


int main(int argc, const char** argv) {

// Classic function pointers
  int (*fp)(int z) = &f; // creating a function pointer value
  int (*gp)(int) = f; // creating a function pointer value
  int (*ffp)(int) = &ff; // creating a function pointer value
  bool b1 = fp != nullptr; // comparison, true
  bool b2 = fp == gp; // comparison, true
  bool b3 = fp != ffp; // comparison, true
  bool b4 = (*fp)(5) == 6; // true
  b4 = fp(5) == 6; // true

  int x = 9;
  b4 = (x == 9? fp: gp)(-1);

  std::cout << b1 << b2 << b3 << b4 << std::endl;
// Method references
  int (P::*mp)() = &P::g;
  int (P::*np)() = &P::h;
  b1 = mp != np;
  b2 = (P(42).*mp)() == 43;
  //b3 = std::invoke(new P(42), mp) == 43;
  std::cout << b1 << b2 << std::endl;


// Lambda expressions
  fp = [](int x){ return x+1; };  
  b1 = fp != gp; // true
  b2 = (*fp)(5) == 6; // true

 // Using a functor object
  Q q;
  b3 = q(4) == 6; // true
  std::cout << b1 << b2 << b3 << std::endl;
}


