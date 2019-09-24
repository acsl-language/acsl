class MyType {
private:
  int myint;
public:
  MyType(int i): myint(i) {}

  //@ ensures \result.myint == this->myint + other.myint;
  MyType operator+(MyType const& other) {
    return MyType(myint + other.myint);
  }
};
