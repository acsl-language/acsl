class A {
  private:
    int x;
  public:
    /*@ requires x > 0;
        assigns \empty;
        ensures \result == x + 1;
    */
    int m() { return x+1; }
};
