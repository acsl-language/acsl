class Array {

  private:

    int* data;
    int data_length;

  public:

    /*@
      requires 0 <= index < data_length;
      ensures \result == data[index];
      pure
    */
    int getValue(int index) {
		return data[index];
    }
};
