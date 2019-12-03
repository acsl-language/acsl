class MyType {
private:
  int myint;
public:
  MyType(int i): myint(i) {}

  //@ ensures \result.myint == \this.myint + other.myint;
  MyType operator+(const MyType & other) const {
    return MyType(myint + other.myint);
  }
};
