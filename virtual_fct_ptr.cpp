#include <iostream>
class A {
  public:
    virtual int m(int x) { return x; }
};

class B: public A {
  public:
    virtual int m(int x) { return x+10; }
};

int main() {
    int (A::* mfp)(int) = &A::m;
    std::cout << (A().*mfp)(1) << std::endl; // prints '1'
    std::cout << (B().*mfp)(1) << std::endl; // prints '11'
}
