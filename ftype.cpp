#include <iostream>
#include <typeinfo>
class B { 
  public : 
    virtual const std::string who() { return "B";} 
};

class A: public B {
  public:
    virtual const std::string who() {return "A"; }
};
  int main() {
    B* b = new B();
    B* bb = new B();
    A* a = new A();
    B* ba = new A();
    const std::type_info& bt = typeid(*b); // *b, NOT b !!
    const std::type_info& bbt = typeid(*bb);
    const std::type_info& at = typeid(*a);
    const std::type_info& bat = typeid(*ba); // type_info of the dynamic type
    
    std::cout << b->who() << bb->who() << a->who() << ba->who() << std::endl;
    std::cout << bt.name() << " " << bbt.name() << " " 
               << at.name() << " " << bat.name() << std::endl;
    // All comparisons are true
    std::cout << (bt==bbt) << " " << (bt!=at) << " " << (bt!=bat) 
                    << " " << (at==bat) << std::endl;
    return 0;
  }

