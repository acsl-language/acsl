namespace A {
   int f; // A::f
   class B {
      static int f; // A::B::f

      //@ predicate pos1() = f > 0;  // A::B::f
      //@ predicate pos2() = A::B::f > 0;  // A::B::f
      //@ predicate pos3() = A::f > 0;  // A::f
      //@ predicate pos4() = B::f > 0;  // A::B::f
   public:
     template <typename T> class C {
     public:
       class D {};
     };
   };
};

// @ predicate pos5() = f > 0;  // not legal
//@ predicate pos6() = A::f > 0;  // A::f
//@ predicate pos7() = A::B::f > 0;  // A::B::f

A::B::C<int>::D x;
