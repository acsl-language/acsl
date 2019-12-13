class C {
private:
  int count;

public:
   /*@ ensures \result == count;
       pure
     @*/
  int getCount() { return count; }


  void test() {
      x:
      count++;
      //@ assert getCount{Here}() == 1 + getCount{x}();
  }
};
